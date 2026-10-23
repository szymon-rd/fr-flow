package frflow.cli

import cats.effect.{ExitCode, IO}
import frflow.api.*
import frflow.protocol.Canonical
import io.circe.Encoder
import io.circe.syntax.*

/** Runs a parsed command against the API: reads print a view (or, `--json`, the typed value), decisions
  * show what they record and are confirmed first (on a terminal, or by `--yes`).
  */
final class Run(api: FrFlowApi, term: Terminal, st: Style):
  import Run.*

  def apply(c: Command): IO[ExitCode] = c match
    case Command.Tree(from, full, json) => api.tree(from).flatMap(t => emit(json, t)(TreeText.lines(t, st, full)))
    case Command.Show(id, lean, json) => api.details(id).flatMap(d => emit(json, d)(NodeText.lines(d, st, lean)))
    case Command.Diff(id, json) => api.diff(id).flatMap(d => emit(json, d)(DiffText.lines(d, st)))
    case Command.Inbox(json) =>
      api.view.flatMap { v =>
        val inbox = Inbox.of(v)
        withTree(v, inbox.overview)(t => emit(json, inbox)(InboxText.lines(inbox, t, st)))
      }
    case Command.Review(as) => ReviewSession(api, term, st).run(as)
    case Command.Accept(nodes, revisit, a) => decision(a)(Decide.Accept(nodes, _, revisit))
    case Command.Reject(node, a) => decision(a)(Decide.Reject(node, _))
    case Command.Confirm(a) => decision(a)(Decide.Confirm(_))
    case Command.Revisit(node, a) => decision(a)(Decide.Revisit(node, _))
    case Command.Gone(node, a) => decision(a)(Decide.Gone(node, _))
    case Command.Ask(node, text, as) => developer(as)(dev => api.ask(node, text, dev).flatMap(done(q =>
      List(s"asked [${q.id}] on ${q.node.fold("the idea")(_.value)}: the agent sees it in its inbox"))))
    case Command.Close(ids) => api.close(ids).flatMap(done(rs => rs.map(r => s"closed [${r.id}]")))
    case Command.Render => api.render.flatMap(r => ok(s"rendered ${r.changed.size} changed file(s); wrote ${r.snapshot}"))
    case Command.Check(node, json) =>
      api.check(node).flatMap(r => withTree(r.view)(t => emit(json, r)(ReportText.check(r, t, st)).as(exit(r.ok))))
    case Command.Status(json) =>
      api.status.flatMap(v => withTree(v)(t => emit(json, v)(ReportText.status(v, t, st)).as(exit(v.ok))))
    case Command.Ci(json) => api.ci.flatMap(r => withTree(r.view)(t => emit(json, r)(ReportText.ci(r, t, st)).as(exit(r.ok))))
    case Command.Context(node) => api.context(node).flatMap(c => term.out(c.text.stripSuffix("\n")).as(ExitCode.Success))
    case Command.Find(query, json) =>
      api.view.flatMap { v =>
        val found = Find(v, query)
        emit(json, found)(ReportText.found(found, v, st))
      }
    case Command.Scaffold(node) =>
      api.scaffold(node).flatMap(s => ok(s.file.fold("nothing to create")(f => s"created $f")))
    case Command.Answer(to, text) => api.answer(to, text).flatMap(done(id => List(s"answered $id")))

  private def withTree[A](v: View, o: Overview)(f: Tree => IO[A]): IO[A] =
    IO.fromEither(Trees.of(v, None, o).left.map(FrFlowError.UnknownNode(_))).flatMap(f)
  private def withTree[A](v: View)(f: Tree => IO[A]): IO[A] = withTree(v, Overview.of(v))(f)

  private def emit[A: Encoder](json: Boolean, a: A)(text: => List[String]): IO[ExitCode] =
    term.out(if json then List(Canonical.file(a.asJson)) else text).as(ExitCode.Success)

  private def ok(line: String) = term.out(line).as(ExitCode.Success)

  private def done[A](lines: A => List[String])(r: Either[Refusal, A]): IO[ExitCode] =
    r.fold(refused, a => term.out(lines(a)).as(ExitCode.Success))

  private def refused(r: Refusal): IO[ExitCode] = term.err(r.message).as(Refused)

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
        api.preview(d, dev).flatMap(_.fold(refused, p => notes(p).flatMap(ns =>
          confirmed(a.yes, (s"This records, as ${dev.name}:" :: ReportText.decided(p, st)) ++ ns, "Record it? [y/N] ").flatMap {
            case Some(true) => api.decide(d, dev).flatMap(done(r => s"Recorded, signed by ${dev.name}:" :: ReportText.decided(r, st)))
            case Some(false) => term.out("Nothing recorded.").as(Refused)
            case None => term.err("a decision is confirmed on a terminal; without one, pass --yes").as(Usage)
          })))
      }
    }

  /** What is not proven, or fails, of the nodes a decision accepts: said before it is confirmed. */
  private def notes(d: Decided): IO[List[String]] = api.view.map(v =>
    d.decisions.filter(_.decision.action.binds).flatMap(l => v.node(l.node).toList.flatMap(_.review.unproven)
      .map(u => st.yellow(s"  note: ${l.node}: $u"))))

  /** True when `--yes` was given or the developer says yes; none when no one can be asked. */
  private def confirmed(yes: Boolean, what: List[String], question: String): IO[Option[Boolean]] =
    if yes then IO.pure(Some(true))
    else if !term.interactive then IO.pure(None)
    else term.out(what) *> term.read(question).map(a => Some(a.exists(x => Yes(x.trim.toLowerCase))))

object Run:
  val Refused: ExitCode = ExitCode(1)
  val Usage: ExitCode = ExitCode(2)
  val Yes: Set[String] = Set("y", "yes")
  def exit(ok: Boolean): ExitCode = if ok then ExitCode.Success else Refused
