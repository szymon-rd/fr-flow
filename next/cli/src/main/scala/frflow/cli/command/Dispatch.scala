package frflow.cli.command

import cats.effect.{ExitCode, IO}
import cats.syntax.all.*
import frflow.api.view.{CheckEvent, Scaffolded, Stop, View}
import frflow.api.{FrFlowApi, Host}
import frflow.cli.review.ReviewSession
import frflow.cli.term.{Exit, Style, Terminal}
import frflow.cli.text.*
import frflow.core.name.NodeId

/** Runs a parsed command on the project open in `host`: a read prints a view, a decision is confirmed first, a check
  * streams its levels on stderr. `layers`: the layers on top; what they add to a view is shown with it, and a warning
  * of theirs fails `status`, `check` and `ci` as FrFlow's do.
  */
final class Dispatch(host: Host[IO], term: Terminal, st: Style, layers: List[CliExtension]):
  private val api: FrFlowApi[IO] = host.api
  private def added(v: View): IO[Contribution] = layers.traverse(_.contribute(host, v, st)).map(_.combineAll)
  private def ok(lines: List[String]): IO[ExitCode] = term.out(lines).as(Exit.Fine)

  def apply(c: Command): IO[ExitCode] = c match
    case Command.Review(as)        => ReviewSession(api, term, st, added, layers.flatMap(_.keys(host))).run(as)
    case Command.Decision(m, n, a) => DecisionCommands(api, term, st).decide(m, n, a)
    case Command.Rebase(as, yes)   => DecisionCommands(api, term, st).rebase(as, yes)
    case Command.Deciders(_)       => term.err("deciders runs before the project is opened").as(Exit.Usage)
    case Command.Layer(run)        => run(host, term, st)
    case other                     => (reads orElse proves)(other)

  private val reads: PartialFunction[Command, IO[ExitCode]] =
    case Command.Tree(from)        => viewed((v, x) => ok(TreeText.lines(v, from, st, x.marks) ++
        ("" :: SummaryText.lines(v, InboxText.waiting(v, x.aside), st, x.waiting))))
    case Command.Show(id, depth)   => viewed((v, x) => v.node(id).fold(gone(v, id))(n =>
        ok(NodeText(v, st, x).lines(n, depth))))
    case Command.Diff(id)          => viewed((v, _) => v.node(id).fold(gone(v, id))(n => api.reading.diff(id)
        .flatMap(d => ok(DiffText.lines(id, d, n.review.decision.isDefined, st)))))
    case Command.Inbox             => viewed((v, x) => ok(InboxText.lines(v, st, x)))
    case Command.Find(q)           => (api.reading.find(q), api.reading.view).flatMapN((f, v) =>
        ok(ReportText.found(q, f, v, st)))

  private val proves: PartialFunction[Command, IO[ExitCode]] =
    case Command.Render => api.proving.render.flatMap(ms => ok(List(s"rendered ${ms.size} changed module(s)")))
    case Command.Check(node, json) => checked(api.proving.check(node), json)((ids, v, x) =>
        (CheckText.check(ids, v, st, x), ids.flatMap(v.node).forall(CheckText.proven) && x.warnings.isEmpty &&
          (node.isDefined || WholeText.fine(v.whole))))
    case Command.Status(json)      => api.proving.status.flatMap(v => added(v).flatMap(x =>
        (if json then api.proving.snapshot.map(List(_)) else IO.pure(TreeText.status(v, st, x)))
          .flatMap(term.out).as(Exit.of(complete(v, x)))))
    case Command.Ci                => checked(api.proving.ci, json = false)((_, v, x) =>
        (CheckText.ci(v, st, x), complete(v, x)))
    case Command.Export            => api.proving.snapshot.flatMap(s => term.out(s)).as(Exit.Fine)
    case Command.Scaffold(id)      => api.proving.scaffold(id).flatMap(s =>
        term.out(ReportText.scaffolded(s)).as(Exit.of(s match
          case Scaffolded.EndNotFound(_) => false
          case _                         => true)))

  private def viewed(f: (View, Contribution) => IO[ExitCode]): IO[ExitCode] =
    api.reading.view.flatMap(v => added(v).flatMap(f(v, _)))

  /** The CI gate: complete, and nothing warned of, FrFlow's or a layer's. */
  private def complete(v: View, x: Contribution): Boolean =
    v.overview.complete && v.warnings.isEmpty && x.warnings.isEmpty

  /** A decided node gone from the model is said so; any other name is unknown. */
  private def gone(v: View, id: NodeId): IO[ExitCode] =
    if v.gone.contains(id) then ok(List(s"$id is gone from the model: it was decided, and the model no longer has " +
      s"it (gone $id -m REASON agrees it is gone)"))
    else IO.raiseError(Stop.UnknownNode(id))

  /** Each level said on stderr as it starts; then what `report` makes of the view the check ends with. */
  private def checked(events: fs2.Stream[IO, CheckEvent], json: Boolean)(
      report: (List[NodeId], View, Contribution) => (List[String], Boolean)): IO[ExitCode] =
    events.evalMap {
      case CheckEvent.Level(i, n, ids) => term.err(st.dim(st.fit(s"check: level $i of $n: ${ids.mkString(", ")}")))
          .as(Option.empty[(List[NodeId], View)])
      case CheckEvent.Done(ids, v)     => IO.pure(Some((ids, v)))
    }.unNone.compile.lastOrError.flatMap((ids, v) => added(v).flatMap { x =>
      val (lines, fine) = report(ids, v, x)
      (if json then api.proving.snapshot.map(List(_)) else IO.pure(lines)).flatMap(term.out).as(Exit.of(fine))
    })
