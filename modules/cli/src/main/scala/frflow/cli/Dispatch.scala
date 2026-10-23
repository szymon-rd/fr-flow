package frflow.cli

import cats.effect.{ExitCode, IO}
import frflow.api.*
import frflow.protocol.*
import io.circe.{Encoder, Json, JsonObject}
import io.circe.syntax.*

/** Runs a parsed command: a read prints a view, or (`--json`) the typed value in brief; a decision is confirmed first. */
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
    case Command.Status(json) => api.status.flatMap(v => withTree(v)(t => emit(json, Brief.status(v))(ReportText.status(v, t, st)).as(exit(v.ok))))
    case Command.Ci => api.ci(progress).flatMap(r => withTree(r.view)(t => ok(ReportText.ci(r, t, st)).as(exit(r.ok))))
    case Command.Find(query) => api.view.flatMap(v => api.find(v, query).flatMap(f => ok(ReportText.found(f, v, st))))
    case Command.Scaffold(node) =>
      api.scaffold(node).flatMap(s => ok(List(s.file.fold(s"nothing to stub: the last check of $node left nothing open that the proof file lacks")(f => s"created $f"))))
    case Command.Answer(to, text) => api.answer(to, text).flatMap(done(id => List(s"answered $id")))

  // On a terminal: a check can take minutes.
  private def progress(p: Progress): IO[Unit] =
    if !term.interactive then IO.unit
    else if p.level == 0 then term.err(st.dim(s"check: building the models (${p.levels} level(s) to prove)"))
    else term.err(st.dim(st.fit(s"check: level ${p.level} of ${p.levels}: ${p.nodes.mkString(", ")}")))

  private def withTree[A](v: View)(f: Tree => IO[A]): IO[A] = IO.fromEither(Trees.of(v, None).left.map(FrFlowError.UnknownNode(_))).flatMap(f)

  private def emit(json: Boolean, j: => Json)(text: => List[String]): IO[ExitCode] = ok(if json then List(Canonical.file(j)) else text)
  private def ok(lines: List[String]) = term.out(lines).as(ExitCode.Success)
  private def done[A](lines: A => List[String])(r: Either[Refusal, A]): IO[ExitCode] = r.fold(refused, a => ok(lines(a)))

  /** Naming no such node or request is a usage error (2), as an unknown node is elsewhere. */
  private def refused(r: Refusal): IO[ExitCode] = term.err(r.message).as(r match
    case Refusal.UnknownNode(_) | Refusal.UnknownRequest(_) => Usage
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

/** A node as `--json` prints it inside a value: without the generated Lean, contents and decisions it carries. */
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

  def status(v: View): Json = Json.obj("overview" -> Overview.of(v).asJson, "warnings" -> v.warnings.asJson, "nodes" -> v.nodes.map(node).asJson)

/** The developer's review: the mechanical batch, each node waiting in the order to decide it, then the gone nodes.
  * The view is read again after each decision, so what it unblocked comes next.
  */
final class ReviewSession(api: FrFlowApi, term: Terminal, st: Style):
  private final case class Pass(skipped: Set[NodeId], batchOffered: Boolean, decided: Int):
    def skip(id: NodeId): Pass = copy(skipped = skipped + id)
    def recorded(n: Int): Pass = copy(decided = decided + n)

  def run(as: Option[String]): IO[ExitCode] =
    if !term.interactive then
      term.err("review is interactive: run it on a terminal (bin/frflow PROJECT review); without one, read inbox and decide with accept or reject --yes")
        .as(Dispatch.Usage)
    else api.developer(as).flatMap(_.fold(r => term.err(r.message).as(Dispatch.Usage), dev => loop(dev, Pass(Set.empty, false, 0))))

  private def loop(dev: Developer, p: Pass): IO[ExitCode] = api.view.flatMap { v =>
    val inbox = Inbox.of(v)
    if !p.batchOffered && inbox.mechanical.nonEmpty then batch(dev, v, inbox, p)
    else inbox.queue.find(w => !p.skipped(w.node.id)) match
      case Some(w) => api.details(v, w.node).flatMap(one(dev, w, _, inbox.queue.count(x => !p.skipped(x.node.id)), p, Depth.Brief))
      case None => inbox.gone.find(g => !p.skipped(g.id)).fold(finish(inbox, p))(gone(dev, _, p))
  }

  private def quit(p: Pass) = api.inbox.flatMap(finish(_, p))
  /** Until the answer is one of `keys` (its first letter counts); none at the end of the input. */
  private def choose(prompt: String, keys: Set[String]): IO[Option[String]] =
    term.read(prompt).flatMap {
      case None => IO.pure(None)
      case Some(a) =>
        val k = a.trim.toLowerCase.take(1)
        if keys(k) then IO.pure(Some(k)) else term.out(st.dim(s"one of: ${keys.toList.sorted.filter(_.nonEmpty).mkString(" ")}")) *> choose(prompt, keys)
    }
  private def reason(prompt: String): IO[Option[String]] = term.read(prompt).map(_.map(_.trim).filter(_.nonEmpty))

  // A refusal is said, and the node skipped.
  private def record(dev: Developer, d: Decide, p: Pass, node: Option[NodeId]): IO[ExitCode] =
    api.decide(d, dev).flatMap {
      case Left(r) => term.out(st.red(s"refused: ${r.message}")) *> loop(dev, node.fold(p)(p.skip))
      case Right(done) =>
        term.out(st.green(s"recorded, signed by ${dev.name}:") :: ReportText.decided(done, st, notes = false)) *> loop(dev, p.recorded(done.decisions.size))
    }

  private def batch(dev: Developer, v: View, inbox: Inbox, p: Pass): IO[ExitCode] =
    val ms = inbox.mechanical
    def changed(r: Reviewed) =
      DiffText.lines(Details.diff(v, r, None), st).drop(1) ++
        r.node.code.filter(_ => r.review.causes.contains(Cause.Code)).map(c => st.dim(s"  code (proven again): ${c.files.mkString(", ")}"))
    term.out("" :: st.bold(s"${ms.size} mechanical decision(s): Lean proves them again, and nothing in them is a choice") ::
      ms.flatMap(r => st.fit(s"  ${st.glyph(r)} ${st.bold(r.id.value)}  ${Lines.statement(r)}") :: changed(r).map(l => st.fit("  " + l)))) *>
      choose("[a]ccept all, with one reason  [s]kip  [q]uit: ", Set("a", "s", "q")).flatMap {
        case Some("a") => reason("Why do they hold (e.g. a new field no rule reads)? ").flatMap {
          case Some(why) => record(dev, Decide.Confirm(why), p.copy(batchOffered = true), None)
          case None => loop(dev, p.copy(batchOffered = true))
        }
        case Some("s") => loop(dev, p.copy(batchOffered = true))
        case _ => finish(inbox, p)
      }

  private def one(dev: Developer, w: Queued, d: NodeDetails, left: Int, p: Pass, depth: Depth): IO[ExitCode] =
    val r = w.node
    val proposal = r.state == ReviewState.Proposed
    val keys = if proposal then "[a]ccept [r]eject [s]kip [v]iew [q]uit [?]ask" else "[a]ccept [s]kip [v]iew [q]uit [?]ask"
    term.out("" :: st.dim(s"${st.rule} $left waiting ${st.rule}") :: NodeText.lines(d, st, depth) ++
      w.followers.map(f => st.dim(s"${st.follows} $f moved only with it: accepting ${r.id} confirms it"))) *>
      choose(s"\n$keys: ", Set("a", "r", "s", "v", "q", "?", "").filter(k => proposal || k != "r")).flatMap {
        case Some("a") => accept(dev, r, p)
        case Some("r") => reason(s"Why not ${r.id}? ").flatMap(_.fold(loop(dev, p))(why =>
          record(dev, Decide.Reject(r.id, why, Some(r.review.version)), p, Some(r.id))))
        case Some("v") => one(dev, w, d, left, p, Depth.Normal)
        case Some("?") => term.read("What should change? ").flatMap {
          case Some(text) if text.trim.nonEmpty => api.ask(Some(r.id), text, dev).flatMap {
            case Left(e) => term.out(st.red(s"refused: ${e.message}"))
            case Right(q) => term.out(List(s"asked [${q.id}]: ${r.id} is with the agent until it answers or changes it"))
          } *> loop(dev, p.skip(r.id))
          case _ => loop(dev, p)
        }
        case Some("s") | Some("") => loop(dev, p.skip(r.id))
        case _ => quit(p)
      }

  /** Asks which decisions below to revisit and why; shows what it records when that is more than the node. */
  private def accept(dev: Developer, r: Reviewed, p: Pass): IO[ExitCode] =
    val candidates = r.review.below.filter(_.kind == BelowKind.Accepted).map(_.id)
    val which =
      if candidates.isEmpty then IO.pure(Nil)
      else term.read(s"Revisit any decision below that this may affect (${candidates.mkString(" ")}; Enter for none)? ")
        .map(_.fold(Nil)(_.split("[\\s,]+").filter(_.nonEmpty).map(NodeId(_)).toList))
    which.flatMap { revisit =>
      reason(s"Why ${r.id}? ").flatMap {
        case None => loop(dev, p)
        case Some(why) =>
          val d = Decide.Accept(List(r.id), why, revisit, Map(r.id -> r.review.version))
          api.preview(d, dev).flatMap {
            case Left(e) => term.out(st.red(s"refused: ${e.message}")) *> loop(dev, p.skip(r.id))
            case Right(plan) if plan.decisions.size <= 1 && plan.unproven.isEmpty => record(dev, d, p, Some(r.id))
            case Right(plan) =>
              term.out("This records:" :: ReportText.decided(plan, st)) *> choose("Record it? [y/n]: ", Set("y", "n")).flatMap {
                case Some("y") => record(dev, d, p, Some(r.id))
                case _ => loop(dev, p)
              }
          }
      }
    }

  private def gone(dev: Developer, g: Gone, p: Pass): IO[ExitCode] =
    term.out("" :: s"${st.bold(g.id.value)} ${st.red("is gone from the model")}: ${g.decision.content.statement}" ::
      st.dim(s"  last ${Words.verb(g.decision.action)} by ${g.decision.by}: ${g.decision.reason}") :: Nil) *>
      choose("[g]one: agree it is gone  [s]kip  [q]uit: ", Set("g", "s", "q", "")).flatMap {
        case Some("g") => reason(s"Why is ${g.id} gone? ").flatMap(_.fold(loop(dev, p))(why => record(dev, Decide.Gone(g.id, why), p, Some(g.id))))
        case Some("s") | Some("") => loop(dev, p.skip(g.id))
        case _ => quit(p)
      }

  private def finish(inbox: Inbox, p: Pass): IO[ExitCode] =
    term.out("" :: s"Decided ${p.decided} decision(s)." :: SummaryText.lines(inbox.overview, st)).as(ExitCode.Success)
