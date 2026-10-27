package frflow.project.program

import cats.effect.IO
import cats.syntax.all.*
import frflow.core.expr.Value
import frflow.core.name.NodeId
import frflow.eval.Semantics
import frflow.eval.run.Broken
import frflow.project.Projects
import frflow.project.pipeline.TestKeys
import frflow.project.port.Records
import frflow.testing.Seed
import frflow.testing.derive.Derive
import frflow.testing.report.*
import frflow.wire.file.Depth

/** Testing before production on rooms in memory: the calendar's Scala tested against each claim on `granted`, the
  * report recorded with its key and not run again while current; the failing cases kept newest first, at most
  * `Kept` a node, none nested deeper than its file may hold.
  */
class TestProgramSuite extends munit.CatsEffectSuite:
  private val claim = NodeId("grantWhenNoOverlap")

  private def tested = for
    p   <- Projects.inMemory(Map.empty)
    a   <- Projects.analysed(p, Projects.rooms, Projects.roomsExamples)
    run  = TestProgram[IO](p.files, Semantics(Projects.rooms), Derive.of(Projects.rooms, Projects.roomsExamples), Nil)
    out <- run(a, None)
  yield (out, run, p)

  test("the calendar's Scala is tested against the claim on granted, every case asked tried, recorded with its key") {
    tested.flatMap { case ((fresh, a), _, p) =>
      val report = fresh.toMap.getOrElse(claim, fail(s"not tested: ${fresh.map(_._1)}"))
      assertEquals((report.count, report.outcome, report.against), (Count(200, 200), Outcome.Passed,
        Against.Claim(claim)))
      assertEquals(a.tested(claim), Some(report))
      assertEquals(a.inputs.recorded.tests.get(claim).map(_._1), Some(TestKeys.of(a, claim)))
      Records.read(p.files).map(r => assertEquals(r.tests, a.inputs.recorded.tests))
    }
  }

  test("a current report is not run again; with only, it is") {
    tested.flatMap { case ((_, a), run, _) =>
      (run(a, None), run(a, Some(claim))).tupled.map((again, only) =>
        assertEquals((again._1, only._1.map(_._1)), (Nil, List(claim))))
    }
  }

  private def failure(i: Int, deep: Int = 0): Failure =
    val nested = (0 until deep).foldLeft[Value](Value.Num(i))((v, _) => Value.Many(List(v)))
    Failure.Call(List(nested), Nil, Broken.Post, Drawn(Seed(1), i, 1))
  private def failed(f: Failure) = TestReport(Count(1, 1), Seed(1), Against.Claim(claim), Outcome.Failed(f), Nil, Nil)

  test("failing cases are kept newest first, at most Kept a node, the same case once") {
    val kept = (0 until 25).foldLeft(Map.empty[NodeId, List[Failure]])((acc, i) =>
      TestProgram.kept(acc, List(claim -> failed(failure(i % 22)))))
    val cases = kept(claim).map(_.from.index)
    assertEquals((cases.size, cases.take(3)), (TestProgram.Kept, List(2, 1, 0)))
  }

  test("a failing case nested deeper than its file may hold is not kept") {
    assertEquals(TestProgram.kept(Map.empty, List(claim -> failed(failure(1, Depth.limit + 5)))), Map.empty)
  }
