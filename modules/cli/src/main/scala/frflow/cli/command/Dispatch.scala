package frflow.cli
package command

import cats.effect.{ExitCode, IO}
import cats.syntax.all.*
import frflow.api.*
import frflow.cli.text.*
import frflow.protocol.*
import io.circe.Json

/** Runs a parsed command: a read prints a view, or (`--json`) the API's value as JSON, in brief; a decision is confirmed first.
  * `layers`, the layers on top: their commands run on `host`, and what they add to a view is shown with it (a warning of
  * theirs fails `status` and `ci` as FrFlow's do). `--json` prints FrFlow's values only.
  */
final class Dispatch(api: FrFlowApi, term: Terminal, st: Style, layers: List[CliExtension] = Nil,
    host: Option[Host] = None):
  import Dispatch.*
  private val on: Host = host.getOrElse(Host(api, java.nio.file.Path.of(".").toAbsolutePath.normalize, Map.empty))
  private def added(v: View): IO[Contribution] = layers.traverse(_.contribute(on, v)).map(Contribution.all)

  def apply(c: Command): IO[ExitCode] = c match
    case Command.Tree(from, json) =>
      api.view.flatMap(added).flatMap(x => api.tree(from).flatMap(t => emit(json, Brief(t))(TreeText.lines(t, st, x))))
    case Command.Show(id, depth, json) =>
      node(id, json)((v, r) => (api.details(v, r), added(v)).flatMapN((d, x) => emit(json, Brief(d))(NodeText.lines(d, st, depth, x))))
    case Command.Diff(id) => node(id, json = false)(api.diff(_, _).flatMap(d => ok(DiffText.lines(d, st))))
    case Command.Inbox(json) =>
      api.view.flatMap(added).flatMap(x => api.reviewing(_ => IO.pure(x.aside))
        .flatMap((v, i) => emit(json, Brief(i))(InboxText.lines(i, v, st, x))))
    case Command.Review(as) => ReviewSession(api, term, st, added).run(as)
    case Command.Decision(make, a) => decision(a)(make)
    case Command.Render => api.render.flatMap(r => ok(List(s"rendered ${r.changed.size} changed file(s); wrote ${r.snapshot}")))
    case Command.Check(node, json) =>
      api.check(node, progress).flatMap(r => added(r.view).flatMap(x =>
        emit(json, Brief(r))(ReportText.check(r, st, x)).as(exit(r.ok && x.warnings.isEmpty))))
    case Command.Status(json) => api.status.flatMap(s => added(s.view).flatMap(x =>
      emit(json, Brief(s))(ReportText.status(s.view, s.tree, st, x)).as(exit(s.ok && x.warnings.isEmpty))))
    case Command.Ci => api.ci(progress).flatMap(r => added(r.view).flatMap(x =>
      ok(ReportText.ci(r, r.tree, st, x)).as(exit(r.ok && x.warnings.isEmpty))))
    case Command.Find(query) => api.view.flatMap(v => api.find(v, query).flatMap(f => ok(ReportText.found(f, v, st))))
    case Command.Scaffold(node) =>
      api.scaffold(node).flatMap(s => ok(List(s.file.fold(s"nothing to stub: the last check of $node left nothing open that the proof file lacks")(f => s"created $f"))))
    case Command.Layer(run) => run(on, term, st)

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

  /** Naming no such node is a usage error (2), as an unknown node is elsewhere. */
  private def refused(r: Refusal): IO[ExitCode] = term.err(r.message).as(r match
    case Refusal.UnknownNode(_) => Usage
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
