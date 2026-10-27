package frflow.testing.model

import cats.Id
import cats.effect.kernel.Sync
import cats.syntax.all.*
import frflow.core.example.Gen
import frflow.core.expr.OutsideFact
import frflow.core.name.NodeId
import frflow.core.spec.NodeKind
import frflow.core.Theory
import frflow.dsl.model.AdapterCheck
import frflow.eval.{Fn, ScalaValue, Semantics}
import frflow.testing.{Draw, Plan, Seed}
import frflow.testing.derive.Always
import frflow.testing.report.{Against, Drawn, Failure, TestReport}

/** A boundary's implementation tested against its model (`stored.checkedAgainst(start = …, observe = …)`): runs of
  * its operations (`Runs`), each from a state of the model drawn by its type and meeting every `always(stored)` about
  * it, on the implementation and on the model (`ModelTests.run`). Run `i` of `cases` is drawn from `(seed, i)` at
  * its size; an outside system (its model assumed) is run at most `OutsideRuns` times, each run starting it afresh.
  * The first run that differs is shrunk: fewer calls, smaller arguments, a smaller state (`RunShrink`).
  */
final class ModelRuns[F[_]: Sync, B[_[_], _[_]], S, A <: B[F, Id]](check: AdapterCheck[F, B, S, A],
    semantics: Semantics, t: Theory):
  private val model = check.model.stateModel
  private val node: Option[NodeId] = t.nodes.map(_.node)
    .find(_.statement.outside.contains(OutsideFact.BehavesAs(model.boundary, model.name))).map(_.id)
  private val outside = node.flatMap(t.node).exists(_.statement.kind == NodeKind.Assumption)
  private val always = Always.of(semantics, t)

  def of(plan: Plan, draw: Draw): F[TestReport] =
    val runs = if outside then plan.settings.cases.min(ModelRuns.OutsideRuns) else plan.settings.cases
    val replayed = plan.replay.collect { case Failure.Run(start, steps, _, from) =>
      (Fn.as[S](semantics.literal(start, model.state)), steps, from) }
    val drawn = (0 until runs).toList.map(i => Drawn(plan.settings.seed, i, Seed.sizeOf(i, runs)))
    val tries = replayed.map(Right(_)) ++ drawn.map(Left(_))
    tries.zipWithIndex.collectFirstSomeM((at, i) => found(at, draw).map(_.map(i -> _))).map { failure =>
      TestReport(failure.fold(tries.size)(_._1 + 1), plan.settings.seed,
        Against.Model(node.getOrElse(NodeId(model.name.value)), 0), failure.map(_._2), Nil, draw.generators)
    }

  /** The run tried (a failing one kept, or one drawn), shrunk when it differs. */
  private def found(at: Either[Drawn, (S, List[Step], Drawn)], draw: Draw): F[Option[Failure]] =
    at.fold(from => drawnRun(draw, from).map((s, steps) => (s, steps, from)), Some(_)).flatTraverse((s, steps, from) =>
      differs(s, steps).flatMap(_.traverse(d => RunShrink(semantics, t, model, fits).smallest(differs, s, steps, d)
        .map((small, run, why) => Failure.Run(semantics.reflect(ScalaValue(small), model.state), run, why, from)))))

  private def differs(s: S, steps: List[Step]): F[Option[Difference]] =
    ModelTests.run(check, semantics, t.vocabulary)(s, steps)

  /** A state meeting every `always(stored)` about the model, then a run of its operations. */
  private def drawnRun(draw: Draw, from: Drawn): Option[(S, List[Step])] =
    val random = from.seed.forCase(from.index)
    for
      start <- Iterator.continually(draw(Gen.Derived[S](model.state), from.size, random)).take(ModelRuns.Tries)
        .flatten.find(fits)
      sig   <- t.vocabulary.boundary(model.boundary)
      steps <- Runs(draw).of(sig, from.size + 2, random)
    yield (start, steps)

  private def fits(s: S): Boolean = always.keeps(model.name, ScalaValue(s))

object ModelRuns:
  /** An outside system is checked on at most this many runs, as today. */
  val OutsideRuns: Int = 200
  /** How many states are drawn before none is found meeting what always holds of the store. */
  val Tries: Int = 50
