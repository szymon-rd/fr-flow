package frflow.testing.model

import cats.MonadThrow
import cats.effect.kernel.Ref
import cats.syntax.all.*
import frflow.core.example.Gen
import frflow.core.expr.{OutsideFact, Prog, Progs, Value}
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.term.Stated
import frflow.core.Theory
import frflow.eval.{ScalaValue, Semantics}
import frflow.testing.{Draw, Plan, Seed}
import frflow.testing.derive.Always
import frflow.testing.report.*

/** A model's operations' plain Scala tested against the model (`implementTested(ops*)(start, observe)(calls)`,
  * whoever wrote it, owner §36): at most `ModelRuns.Runs` runs of its operations (`Runs`), each from a state of the
  * model drawn by its type and meeting every `always(stored)` about it, on the Scala and on the model
  * (`ModelTests.run`). Run `i` is drawn from `(seed, i)` at its size; a run that cannot be drawn is not tried, and the
  * shortfall said. The first run that differs is shrunk (`RunShrink`). What the runs reach is counted: each operation
  * called, each branch of the model's steps taken both ways. Reported under the assumption that nothing outside the
  * code changes the model's state, when there is one.
  */
final class ModelRuns[F[_]: MonadThrow: Ref.Make](check: ModelTests.Check, semantics: Semantics, t: Theory):
  private type Tried = Either[Drawn, (Value, List[Step], Drawn)]
  private val model = check.model
  private val typing = Typing(semantics, t.vocabulary)
  private val always = Always.of(semantics, t)
  private val ops: List[SymbolName] = model.ops.map(_.op)
  private val branches: Map[SymbolName, List[Prog[Stated[?]]]] = model.ops.map(o =>
    o.op -> Progs.all(o.steps).collect { case b @ Prog.Branch(_, _, _) => b }).toMap
  private val node: NodeId = ModelRuns.node(t, check)

  def of(plan: Plan, draw: Draw): F[TestReport] =
    val runs = plan.settings.cases.min(ModelRuns.Runs)
    val replayed: List[Tried] = plan.replay.collect { case Failure.Run(start, steps, _, from) =>
      Right((start, steps, from)) }
    val drawn: List[Tried] = (0 until runs).toList.map(i => Left(Drawn(plan.settings.seed, i, Seed.sizeOf(i, runs))))
    for
      hits    <- Ref.of[F, Hits](Hits.zero(targets))
      tried   <- (replayed ++ drawn, 0).tailRecM((left, n) => left match
        case Nil            => (n, Option.empty[Failure]).asRight[(List[Tried], Int)].pure[F]
        case first :: rest  => attempt(first, draw, hits).map {
            case None          => (rest, n).asLeft
            case Some(None)    => (rest, n + 1).asLeft
            case Some(Some(f)) => (n + 1, Some(f)).asRight
          })
      reached <- hits.get
    yield TestReport(Count(replayed.size + runs, tried._1), plan.settings.seed, Against.Model(node, model.name),
      tried._2.fold(Outcome.Passed)(Outcome.Failed(_)), reached.unreached, draw.notes)

  /** Every operation called, every branch of the model's steps taken each way. */
  private def targets: List[Target] = ops.zipWithIndex.flatMap((op, i) =>
    Target(Position(List(i)), Reach.Called(op)) :: branches.getOrElse(op, Nil).indices.toList.flatMap(k =>
      List(true, false).map(held => Target(Position(List(i, k)), Reach.Branch(held)))))

  /** A run tried: not drawn (none), passed, or the failure found, shrunk. */
  private def attempt(at: Tried, draw: Draw, hits: Ref[F, Hits]): F[Option[Option[Failure]]] =
    at.fold(from => drawnRun(draw, from).map((s, steps) => (s, steps, from)), Some(_)).traverse((s, steps, from) =>
      differs(hits)(s, steps).flatTap(d => hits.update(_ |+| called(steps, d))).flatMap(_.traverse(d =>
        RunShrink(typing, always, model, t.vocabulary).smallest(differs(hits), s, steps, d)
          .map((small, run, why) => Failure.Run(small, run, why, from)))))

  private def differs(hits: Ref[F, Hits])(s: Value, steps: List[Step]): F[Option[Difference]] =
    ModelTests.run(check, semantics, t.vocabulary, branched(hits))(typing.literal(s, model.state), steps)

  private def branched(hits: Ref[F, Hits])(op: SymbolName, p: Prog[Stated[?]], held: Boolean): F[Unit] =
    val at = (ops.indexOf(op), branches.getOrElse(op, Nil).indexWhere(_ eq p))
    if at._1 < 0 || at._2 < 0 then MonadThrow[F].unit
    else hits.update(_ |+| Hits.of(Target(Position(List(at._1, at._2)), Reach.Branch(held))))

  /** The operations a run called: up to the call done differently, or all of them. */
  private def called(steps: List[Step], d: Option[Difference]): Hits =
    val upTo = d.collect { case Difference.Call(st, _, _) => steps.indexOf(st) + 1 }.getOrElse(steps.size)
    steps.take(upTo).foldMap(st => Hits.of(Target(Position(List(ops.indexOf(st.op))), Reach.Called(st.op))))

  /** A state meeting every `always(stored)` about the model, then a run of its operations. */
  private def drawnRun(draw: Draw, from: Drawn): Option[(Value, List[Step])] =
    val random = from.seed.forCase(from.index)
    for
      start <- Iterator.continually(draw(Gen.Derived[Any](model.state), from.size, random)).take(ModelRuns.Tries)
        .flatten.find(s => always.keeps(model.name, ScalaValue(s)))
      steps <- Runs(draw, typing).of(model, from.size + 2, random)
    yield (typing.reflect(ScalaValue(start), model.state), steps)

object ModelRuns:
  /** The runs a model's operations' Scala is tested on, at most: 200 by default. */
  val Runs: Int = 200
  /** How many states are drawn before none is found meeting what always holds of the store. */
  val Tries: Int = 50

  /** A node's runs, of each model whose Scala is reported under it, as one report: the cases summed, the first
    * failure, what none reached.
    */
  def joined(a: TestReport, b: TestReport): TestReport =
    TestReport(Count(a.count.asked + b.count.asked, a.count.tried + b.count.tried), a.seed, a.against,
      if a.outcome == Outcome.Passed then b.outcome else a.outcome, a.unreached.filter(b.unreached.contains),
      (a.notes ++ b.notes).distinct)

  /** The node a model's runs are reported under: the assumption that nothing outside the code changes its state, or,
    * with none, one named as the model.
    */
  def node(t: Theory, check: ModelTests.Check): NodeId = t.nodes.map(_.node)
    .find(_.statement.outside.contains(OutsideFact.OnlyCodeChanges(check.model.name)))
    .fold(NodeId(check.model.name.value))(_.id)
