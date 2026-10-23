package frflow.cli

import cats.effect.{ExitCode, IO}
import frflow.api.*
import frflow.protocol.*
import io.circe.{Codec, Encoder, Json}
import io.circe.derivation.ConfiguredCodec
import io.circe.syntax.*

/** Runs a parsed command: a read prints a view, or (`--json`) the typed value in brief; a decision is confirmed first. */
final class Dispatch(api: FrFlowApi, term: Terminal, st: Style):
  import Dispatch.*

  def apply(c: Command): IO[ExitCode] = c match
    case Command.Tree(from, json) => api.tree(from).flatMap(t => emit(json, Brief(t))(TreeText.lines(t, st)))
    case Command.Show(id, depth, json) =>
      node(id, json)(api.details(_, _).flatMap(d => emit(json, Brief(d))(NodeText.lines(d, st, depth))))
    case Command.Diff(id) => node(id, json = false)(api.diff(_, _).flatMap(d => ok(DiffText.lines(d, st))))
    case Command.Inbox(json) => api.reviewing.flatMap((v, i) => emit(json, Brief(i))(InboxText.lines(i, v, st)))
    case Command.Review(as) => ReviewSession(api, term, st).run(as)
    case Command.Decision(make, a) => decision(a)(make)
    case Command.Ask(node, text, as) => developer(as)(dev => api.ask(node, text, dev).flatMap(done(q =>
      List(s"asked [${q.id}] on ${q.node.fold("the idea")(_.value)}: the agent sees it in its inbox"))))
    case Command.Close(ids) => api.close(ids).flatMap(done(rs => rs.map(r => s"closed [${r.id}]")))
    case Command.Render => api.render.flatMap(r => ok(List(s"rendered ${r.changed.size} changed file(s); wrote ${r.snapshot}")))
    case Command.Check(node, json) =>
      api.check(node, progress).flatMap(r => emit(json, Brief(r))(ReportText.check(r, st)).as(exit(r.ok)))
    case Command.Status(json) => api.status.flatMap(s => emit(json, Brief(s))(ReportText.status(s.view, s.tree, st)).as(exit(s.ok)))
    case Command.Ci => api.ci(progress).flatMap(r => ok(ReportText.ci(r, r.tree, st)).as(exit(r.ok)))
    case Command.Find(query) => api.view.flatMap(v => api.find(v, query).flatMap(f => ok(ReportText.found(f, v, st))))
    case Command.Scaffold(node) =>
      api.scaffold(node).flatMap(s => ok(List(s.file.fold(s"nothing to stub: the last check of $node left nothing open that the proof file lacks")(f => s"created $f"))))
    case Command.Answer(to, text) => api.answer(to, text).flatMap(done(id => List(s"answered $id")))
    case Command.Said(text) => api.said(text).flatMap(done(_ => List("recorded what the developer said")))
    case Command.QuestionAsked(text, assumed) =>
      api.asked(text, assumed).flatMap(done(q => List(s"recorded [${q.id}]: ask it in chat, with the answer you assume")))
    case Command.Replied(q, text) => api.replied(q, text).flatMap(done(x => List(s"recorded the reply to [${x.id}]")))
    case Command.Conversation(json) =>
      api.view.flatMap(v => emit(json, v.conversation.asJson)(ConversationText.lines(v.conversation, st)))

  /** A node in the model; or one gone from it, shown as gone with its last decision. */
  private def node(id: NodeId, json: Boolean)(f: (View, Reviewed) => IO[ExitCode]): IO[ExitCode] = api.view.flatMap(v =>
    v.node(id).map(f(v, _)).orElse(Details.gone(v, id).map(g => emit(json, Brief(g))(GoneText.lines(g, st))))
      .getOrElse(IO.raiseError(FrFlowError.UnknownNode(id))))

  // On a terminal: a check can take minutes.
  private def progress(p: Progress): IO[Unit] =
    if !term.interactive then IO.unit
    else if p.level == 0 then term.err(st.dim(s"check: building the models (${p.levels} level(s) to prove)"))
    else term.err(st.dim(st.fit(s"check: level ${p.level} of ${p.levels}: ${p.nodes.mkString(", ")}")))

  private def emit(json: Boolean, j: => Json)(text: => List[String]): IO[ExitCode] = ok(if json then List(Canonical.file(j)) else text)
  private def ok(lines: List[String]) = term.out(lines).as(ExitCode.Success)
  private def done[A](lines: A => List[String])(r: Either[Refusal, A]): IO[ExitCode] = r.fold(refused, a => ok(lines(a)))

  /** Naming no such node or request, or asking nothing, is a usage error (2), as an unknown node is elsewhere. */
  private def refused(r: Refusal): IO[ExitCode] = term.err(r.message).as(r match
    case Refusal.UnknownNode(_) | Refusal.UnknownRequest(_) | Refusal.NoRequest(_) | Refusal.NoText | Refusal.UnknownQuestion(_) |
        Refusal.NoAssumption => Usage
    case _ => Refused)

  private def developer(as: Option[String])(f: Developer => IO[ExitCode]): IO[ExitCode] =
    api.developer(as).flatMap(_.fold(r => term.err(r.message).as(Usage), f))

  /** The reason given or asked for; what `make` records, confirmed by `--yes` or on a terminal; then recorded. */
  private def decision(a: Asked)(make: String => Decide): IO[ExitCode] =
    def typed(r: Option[String]) = r.map(_.trim).filter(_.nonEmpty)
    val reason = if typed(a.reason).isDefined || !term.interactive then IO.pure(typed(a.reason))
      else term.read("Why (kept as part of the theory)? ").map(typed)
    reason.flatMap {
      case None => term.err("give the reason: --reason TEXT (it is kept as part of the theory)").as(Usage)
      case Some(reason) => developer(a.as) { dev =>
        val d = make(reason)
        // None: no one can be asked.
        def confirmed(p: Decided): IO[Option[Boolean]] =
          if a.yes then IO.pure(Some(true))
          else if !term.interactive then IO.pure(None)
          else term.out(s"This records, as ${dev.name}:" :: ReportText.decided(p, st)) *>
            term.read("Record it? [y/N] ").map(x => Some(x.exists(y => Set("y", "yes")(y.trim.toLowerCase))))
        api.preview(d, dev).flatMap(_.fold(refused, confirmed(_).flatMap {
          case Some(true) => api.decide(d, dev).flatMap(done(r => s"Recorded, signed by ${dev.name}:" :: ReportText.decided(r, st, notes = false)))
          case Some(false) => term.out("Nothing recorded.").as(Refused)
          case None => term.err("a decision is confirmed on a terminal; without one, pass --yes").as(Usage)
        }))
      }
    }

object Dispatch:
  val Refused: ExitCode = ExitCode(1)
  val Usage: ExitCode = ExitCode(2)
  def exit(ok: Boolean): ExitCode = if ok then ExitCode.Success else Refused

/** `--json`: a value as the API returns it, with each node in it in brief, and each decision without the content and
  * chain it was bound to (the node shown keeps its own content).
  */
trait Brief[A]:
  def apply(a: A): Json

object Brief:
  def apply[A](a: A)(using b: Brief[A]): Json = b(a)

  /** A node inside a value: without the generated Lean, contents and decisions it carries. */
  final case class NodeBrief(id: NodeId, kind: String, state: ReviewState, causes: List[Cause], status: Option[CheckStatus],
      statement: String, waitsFor: Option[NodeId], unproven: List[String]) derives Encoder.AsObject
  def node(r: Reviewed): NodeBrief =
    NodeBrief(r.id, r.node.shownKind, r.state, r.review.causes, r.node.status, r.node.content.statement, r.review.waitsFor, r.review.unproven)

  /** A view as `status` prints it: the counts, the warnings, each node. */
  final case class StatusBrief(overview: Overview, warnings: List[String], nodes: List[NodeBrief]) derives Encoder.AsObject

  // Within these, the values are encoded as the API's codecs do, but for a node and a decision.
  private given Encoder[Reviewed] = Encoder[NodeBrief].contramap(node)
  private given Encoder[Decision] = summon[ConfiguredCodec[Decision]].mapJsonObject(_.remove("content").remove("chain").remove("sig"))
  private given Encoder.AsObject[Gone] = Encoder.AsObject.derived
  private given Encoder.AsObject[Queued] = Encoder.AsObject.derived
  private given Encoder.AsObject[TreeNode] = Encoder.AsObject.derived
  private given Encoder.AsObject[Review] = Encoder.AsObject.derived
  private given Encoder.AsObject[NodeDiff] = Encoder.AsObject.derived
  private def of[A](e: Encoder[A]): Brief[A] = e(_)

  given Brief[Tree] = of(Encoder.AsObject.derived[Tree])
  /** A gone node keeps the content it was decided with: there is nothing else of it. */
  given Brief[GoneNode] = of(summon[Codec.AsObject[GoneNode]])
  given Brief[Inbox] = of(Encoder.AsObject.derived[Inbox])
  private def status(v: View, o: Overview) = StatusBrief(o, v.warnings, v.nodes.map(node)).asJson
  given Brief[StatusReport] = s => status(s.view, s.tree.overview)
  given Brief[CheckReport] = r => Json.obj("checked" -> r.nodes.asJson, "status" -> status(r.view, r.overview))

  /** A node's details: the node itself in full, less its generated Lean; the nodes around it in brief. */
  given Brief[NodeDetails] =
    val around = Encoder.AsObject.derived[NodeDetails]
    d =>
      val n = d.node.node.copy(lean = "", holds = "", obligations = Nil, proof = None)
      val full = Json.obj("node" -> n.asJson, "review" -> d.node.review.asJson)
      Json.fromJsonObject(("node" -> full) +: around.encodeObject(d).remove("node"))
