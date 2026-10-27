package frflow.api.shell

import cats.Parallel
import cats.effect.{Async, Ref}
import cats.syntax.all.*
import frflow.project.check.CheckProgram
import frflow.project.pipeline.{Analysis, Recorded, Testable}
import frflow.project.program.TestProgram

/** The analysis an acceptance is decided on: every node checked by Lean and tested afresh by this process, since what
  * is recorded on disk (`checks.json`, `tests.json`) may have been written by anyone; what this process found is
  * reused while every check and report of it is current (nothing it depends on moved). The failing cases kept
  * (`counterexamples.json`) are only replayed first, so they are read as they are.
  */
private[api] final class Fresh[F[_]: Async: Parallel](s: Session[F], found: Ref[F, Option[Recorded]]):
  def analysis: F[Analysis] = s.analysis.flatMap(a =>
    found.get.map(_.map(a.withRecorded).filter(current)).flatMap(_.fold(again(a))(_.pure[F])))

  private def again(a: Analysis): F[Analysis] =
    val cleared = a.withRecorded(Recorded.none.copy(counterexamples = a.inputs.recorded.counterexamples))
    for
      lake         <- s.lean(a)
      (_, checked) <- s.guarded(CheckProgram(s.ports.files, lake, s.library.path, s.code)(cleared, None))
      (_, tested)  <- s.guarded(TestProgram(s.ports.files, s.code, s.models)(checked, None))
      _            <- found.set(Some(tested.inputs.recorded))
    yield tested

  /** Each node Lean is asked anything of checked, the theory's check current (or none made), and each node with
    * tests tested, under the records given.
    */
  private def current(b: Analysis): Boolean =
    val t = b.decided.theory
    val tested = t.nodes.map(_.node.id).filter(Testable.of(t, _)) ++ s.models.map(_.node)
    b.obligations.forall(o => b.current(o.node).isDefined) &&
      b.inputs.recorded.checks.whole.forall(_ => b.wholeCheck.isDefined) && tested.forall(b.tested(_).isDefined)
