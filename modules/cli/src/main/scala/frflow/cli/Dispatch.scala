package frflow.cli

import cats.effect.{ExitCode, IO}
import frflow.api.*
import frflow.protocol.*
import io.circe.{Encoder, Json, JsonObject}
import io.circe.syntax.*

/** Runs a parsed command against the API: reads print a view (or, `--json`, the typed value in brief),
  * decisions show what they record and are confirmed first (on a terminal, or by `--yes`).
  */
final class Dispatch(api: FrFlowApi, term: Terminal, st: Style):
  import Dispatch.*

  def apply(c: Command): IO[ExitCode] = c match
    case Command.Tree(from, json) => api.tree(from).flatMap(t => emit(json, Brief(t.asJson))(TreeText.lines(t, st)))
    case Command.Show(id, depth, json) => api.details(id).flatMap(d => emit(json, Brief.details(d))(NodeText.lines(d, st, depth)))
    case Command.Diff(id) => api.diff(id).flatMap(d => ok(DiffText.lines(d, st)))
    case Command.Inbox(json) => api.inbox.flatMap(i => emit(json, Brief(i.asJson))(InboxText.lines(i, st)))
    case Command.Review(as) => ReviewSession(api, term, st).run(as)
    case Command.Decision(make, a) => decision(a)(make)
    case Command.Ask(node, text, as) => developer(as)(dev => api.ask(node, text, dev).flatMap(done(q =>
      List(s"asked [${q.id}] on ${q.node.fold("the idea")(_.value)}: the agent sees it in its inbox"))))
    case Command.Close(ids) => api.close(ids).flatMap(done(rs => rs.map(r => s"closed [${r.id}]")))
    case Command.Render => api.render.flatMap(r => ok(List(s"rendered ${r.changed.size} changed file(s); wrote ${r.snapshot}")))
    case Command.Check(node, json) =>
      api.check(node, progress).flatMap(r => emit(json, Json.obj("checked" -> r.nodes.asJson, "status" -> Brief.status(r.view)))(
        ReportText.check(r, st)).as(exit(r.ok)))
    case Command.Status(json) =>
      api.status.flatMap(v => withTree(v)(t => emit(json, Brief.status(v))(ReportText.status(v, t, st)).as(exit(v.ok))))
    case Command.Ci => api.ci(progress).flatMap(r => withTree(r.view)(t => ok(ReportText.ci(r, t, st)).as(exit(r.ok))))
    case Command.Find(query) => api.view.flatMap(v => api.find(v, query).flatMap(f => ok(ReportText.found(f, v, st))))
    case Command.Scaffold(node) =>
      api.scaffold(node).flatMap(s => ok(List(s.file.fold(s"nothing to stub: the last check of $node left nothing open that the proof file lacks")(f => s"created $f"))))
    case Command.Answer(to, text) => api.answer(to, text).flatMap(done(id => List(s"answered $id")))

  /** One line per level of a check, on a terminal: a check can take minutes. */
  private def progress(p: Progress): IO[Unit] =
    if !term.interactive then IO.unit
    else if p.level == 0 then term.err(st.dim(s"check: building the models (${p.levels} level(s) to prove)"))
    else term.err(st.dim(st.fit(s"check: level ${p.level} of ${p.levels}: ${p.nodes.mkString(", ")}")))

  private def withTree[A](v: View)(f: Tree => IO[A]): IO[A] =
    IO.fromEither(Trees.of(v, None, Overview.of(v)).left.map(FrFlowError.UnknownNode(_))).flatMap(f)

  private def emit(json: Boolean, j: => Json)(text: => List[String]): IO[ExitCode] =
    ok(if json then List(Canonical.file(j)) else text)

  private def ok(lines: List[String]) = term.out(lines).as(ExitCode.Success)

  private def done[A](lines: A => List[String])(r: Either[Refusal, A]): IO[ExitCode] = r.fold(refused, a => ok(lines(a)))

  /** A refusal exits 1; naming no such node or request is a usage error (2), as an unknown node is elsewhere. */
  private def refused(r: Refusal): IO[ExitCode] = term.err(r.message).as(r match
    case Refusal.UnknownNode(_) | Refusal.UnknownRequest(_) => Usage
    case _ => Refused)

  private def developer(as: Option[String])(f: Developer => IO[ExitCode]): IO[ExitCode] =
    api.developer(as).flatMap(_.fold(r => term.err(r.message).as(Usage), f))

  /** The reason given, or asked for on a terminal. */
  private def reasonOf(typed: Option[String]): IO[Option[String]] =
    typed.map(_.trim).filter(_.nonEmpty) match
      case Some(r) => IO.pure(Some(r))
      case None if term.interactive => term.read("Why (kept as part of the theory)? ").map(_.map(_.trim).filter(_.nonEmpty))
      case None => IO.pure(None)

  /** Shows what `make` records, asks for confirmation (or takes `--yes`), then records it. */
  private def decision(a: Asked)(make: String => Decide): IO[ExitCode] =
    reasonOf(a.reason).flatMap {
      case None => term.err("give the reason: --reason TEXT (it is kept as part of the theory)").as(Usage)
      case Some(reason) => developer(a.as) { dev =>
        val d = make(reason)
        api.preview(d, dev).flatMap(_.fold(refused, p =>
          confirmed(a.yes, s"This records, as ${dev.name}:" :: ReportText.decided(p, st), "Record it? [y/N] ").flatMap {
            case Some(true) => api.decide(d, dev).flatMap(done(r => s"Recorded, signed by ${dev.name}:" :: ReportText.decided(r, st, notes = false)))
            case Some(false) => term.out("Nothing recorded.").as(Refused)
            case None => term.err("a decision is confirmed on a terminal; without one, pass --yes").as(Usage)
          }))
      }
    }

  /** True when `--yes` was given or the developer says yes; none when no one can be asked. */
  private def confirmed(yes: Boolean, what: List[String], question: String): IO[Option[Boolean]] =
    if yes then IO.pure(Some(true))
    else if !term.interactive then IO.pure(None)
    else term.out(what) *> term.read(question).map(a => Some(a.exists(x => Yes(x.trim.toLowerCase))))

object Dispatch:
  val Refused: ExitCode = ExitCode(1)
  val Usage: ExitCode = ExitCode(2)
  val Yes: Set[String] = Set("y", "yes")
  def exit(ok: Boolean): ExitCode = if ok then ExitCode.Success else Refused

/** A node as `--json` prints the nodes a value holds: not the generated Lean, contents and decisions it carries. */
final case class NodeBrief(id: NodeId, kind: String, state: ReviewState, causes: List[Cause], status: Option[CheckStatus],
    statement: String, waitsFor: Option[NodeId], unproven: List[String]) derives Encoder.AsObject

object Brief:
  def node(r: Reviewed): NodeBrief =
    NodeBrief(r.id, r.node.shownKind, r.state, r.review.causes, r.node.status, r.node.content.statement, r.review.waitsFor, r.review.unproven)

  /** `j` with each node in it in brief, and each decision without the content and chain it was bound to. */
  def apply(j: Json): Json = j.arrayOrObject(j, a => Json.fromValues(a.map(apply)), o =>
    if o.contains("node") && o.contains("review") then Json.fromJsonObject(o).as[Reviewed].fold(_ => Json.fromJsonObject(o.mapValues(apply)), node(_).asJson)
    else if o.contains("action") && o.contains("by") then Json.fromJsonObject(o.remove("content").remove("chain").remove("sig"))
    else Json.fromJsonObject(o.mapValues(apply)))

  /** A node's details: the node itself in full, less its generated Lean; the nodes around it in brief. */
  def details(d: NodeDetails): Json =
    val n = d.node.node.copy(lean = "", holds = "", obligations = Nil, proof = None)
    val around = apply(d.asJson).asObject.fold(JsonObject.empty)(_.remove("node"))
    Json.fromJsonObject(("node" -> Json.obj("node" -> n.asJson, "review" -> apply(d.node.review.asJson))) +: around)

  /** Where the knowledge base stands: the summary, the warnings, each node in brief. */
  def status(v: View): Json =
    Json.obj("overview" -> Overview.of(v).asJson, "warnings" -> v.warnings.asJson, "nodes" -> v.nodes.map(node).asJson)
