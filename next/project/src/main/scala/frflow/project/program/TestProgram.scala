package frflow.project.program

import cats.effect.kernel.Sync
import cats.syntax.all.*
import frflow.core.name.NodeId
import frflow.eval.Semantics
import frflow.project.pipeline.{Analysis, Testable, TestKeys}
import frflow.project.port.{ProjectFiles, Records}
import frflow.testing.{Draw, Plan, PropertyTests}
import frflow.testing.report.{Failure, TestReport}
import frflow.wire.file.{Depth, Files}
import frflow.wire.test.TestsFile

/** Testing before production: each node's plain Scala against it (`PropertyTests`, the examples' cases counted
  * first) and each store's implementations given against its model (`ModelCheck`), for the nodes whose report is not
  * current (or `only`); the failing cases kept first. It runs the developer's code, so `Sync`. Its records are
  * written: the reports (`tests.json`) and, newest first, at most `Kept` failing cases a node, each nested no deeper
  * than the file may be (`counterexamples.json`).
  */
final class TestProgram[F[_]: Sync](files: ProjectFiles[F], semantics: Semantics, draw: Draw,
    models: List[ModelCheck[F]]):
  def apply(a: Analysis, only: Option[NodeId]): F[(List[(NodeId, TestReport)], Analysis)] =
    val t = a.decided.theory
    val all = (t.nodes.map(_.node.id).filter(Testable.of(t, _)) ++ models.map(_.node)).distinct
    val todo = all.filter(id => only.fold(a.tested(id).isEmpty)(_ == id))
    for
      fresh <- todo.traverseFilter(id => run(a, id).map(_.map(id -> _)))
      kept   = a.inputs.recorded.tests.filter((id, _) => all.contains(id))
      tests  = kept ++ fresh.map((id, r) => id -> (TestKeys.of(a, id), r))
      failed = TestProgram.kept(a.inputs.recorded.counterexamples, fresh)
      _     <- Records.writeTests(files, tests)
      _     <- Records.writeFailures(files, failed).whenA(failed != a.inputs.recorded.counterexamples)
    yield (fresh, a.withRecorded(a.inputs.recorded.copy(tests = tests, counterexamples = failed)))

  /** Its report: from its store's implementations, or from its plain code; none when nothing tests it. */
  private def run(a: Analysis, id: NodeId): F[Option[TestReport]] =
    val plan = Plan(a.inputs.settings, a.inputs.recorded.counterexamples.getOrElse(id, Nil))
    models.filter(_.node == id).traverse(_.run(plan, draw)).flatMap(rs => rs.reduceLeftOption(
      frflow.testing.model.ModelRuns.joined).fold(Sync[F].blocking(PropertyTests(semantics, a.decided.theory)
        .of(id, plan, draw, a.computed.examples.map(_._1))))(r => Sync[F].pure(Some(r))))

object TestProgram:
  /** At most this many failing cases are kept a node. */
  val Kept: Int = 20

  /** The failing cases kept: each new one first, the one drawn at the same place dropped; one nested deeper than
    * `counterexamples.json` may hold is not kept.
    */
  def kept(before: Map[NodeId, List[Failure]], found: List[(NodeId, TestReport)]): Map[NodeId, List[Failure]] =
    found.foldLeft(before) { case (acc, (id, r)) =>
      r.failure.filter(f => Depth.beyond(Files.json(TestsFile.counterexamples, Map(id -> List(f)))).isEmpty)
        .fold(acc)(f => acc.updated(id, (f :: acc.getOrElse(id, Nil).filterNot(_.from == f.from)).take(Kept)))
    }
