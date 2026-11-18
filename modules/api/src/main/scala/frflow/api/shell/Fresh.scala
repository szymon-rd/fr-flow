package frflow.api.shell

import cats.Parallel
import cats.effect.{Async, Ref}
import cats.syntax.all.*
import frflow.project.check.CheckProgram
import frflow.project.pipeline.{Analysis, Recorded, Testable}
import frflow.project.program.TestProgram

/** The analysis a decision that keeps nodes is taken on, from what this process found itself, since what is recorded
  * on disk (`checks.json`, `tests.json`) may have been written by anyone. A confirmation (`analysis`): every node
  * checked by Rocq and tested afresh, since a mechanical batch is accepted because Rocq proves it again; reused while
  * every check and report of it is current (nothing it depends on moved). An acceptance (`tested`): only the code
  * tested afresh, since it is refused only for code that fails or is not tested, and binds to what a node says and
  * its code, never to what Rocq shows: no Rocq is run for it. The failing cases kept (`counterexamples.json`) are
  * only replayed first, so they are read as they are.
  */
private[api] final class Fresh[F[_]: Async: Parallel](s: Session[F], found: Ref[F, Option[Recorded]]):
  def analysis: F[Analysis] = s.analysis.flatMap(a =>
    found.get.map(_.map(a.withRecorded).filter(current)).flatMap(_.fold(again(a))(_.pure[F])))

  def tested: F[Analysis] = s.analysis.flatMap(a =>
    found.get.map(_.map(a.withRecorded).filter(current)).flatMap(_.fold(testedAgain(a))(_.pure[F])))

  private def testedAgain(a: Analysis): F[Analysis] =
    val cleared = a.withRecorded(Recorded.none.copy(counterexamples = a.inputs.recorded.counterexamples))
    s.guarded(TestProgram(s.ports.files, s.code)(cleared, None)).map(_._2)

  private def again(a: Analysis): F[Analysis] =
    val cleared = a.withRecorded(Recorded.none.copy(counterexamples = a.inputs.recorded.counterexamples))
    for
      prover       <- s.prover(a)
      (_, checked) <- s.guarded(CheckProgram(s.ports.files, prover, s.code)(cleared, None))
      (_, tested)  <- s.guarded(TestProgram(s.ports.files, s.code)(checked, None))
      _            <- found.set(Some(tested.inputs.recorded))
    yield tested

  /** Each node Rocq is asked anything of checked, the theory's check current (or none made), and each node with
    * tests tested, under the records given.
    */
  private def current(b: Analysis): Boolean =
    val t = b.decided.theory
    val tested = t.nodes.map(_.node.id).filter(Testable.of(t, _))
    b.obligations.forall(o => b.current(o.node).isDefined) &&
      b.inputs.recorded.checks.whole.forall(_ => b.wholeCheck.isDefined) && tested.forall(b.tested(_).isDefined)
