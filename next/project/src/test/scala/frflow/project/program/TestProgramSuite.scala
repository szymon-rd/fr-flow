package frflow.project.program

import cats.effect.IO
import cats.syntax.all.*
import frflow.core.expr.Value
import frflow.core.name.NodeId
import frflow.eval.run.Broken
import frflow.project.{Projects, Tables}
import frflow.project.pipeline.TestKeys
import frflow.project.port.RunCode
import frflow.project.port.Records
import frflow.testing.Seed
import frflow.testing.report.*
import frflow.wire.file.Depth
import frflow.decision.review.Unproven
import frflow.eval.Semantics
import rooms.storedBookings

/** Testing before production on rooms in memory: the calendar's Scala tested against each claim on `granted`, the
  * report recorded with its key and not run again while current; the failing cases kept newest first, at most
  * `Kept` a node, none nested deeper than its file may hold.
  */
class TestProgramSuite extends munit.CatsEffectSuite:
  private val claim = NodeId("grantWhenNoOverlap")

  private def tested = for
    p   <- Projects.inMemory(Map.empty)
    a   <- Projects.analysed(p, Projects.rooms, Projects.roomsExamples)
    run  = TestProgram[IO](p.files, RunCode.inline[IO], Nil)
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

  private val model = frflow.testing.model.ModelRuns.reportedUnder(storedBookings.name)

  /** The table's assumption tested by the Scala given, as the project's checks (`Tables`) give it. */
  private def modelled(checks: List[ModelCheck[IO]]) = for
    p   <- Projects.inMemory(Map.empty)
    a   <- Projects.analysed(p, Projects.rooms, Projects.roomsExamples)
    out <- TestProgram[IO](p.files, RunCode.inline[IO], checks)(a, Some(model))
  yield out

  test("each Scala of a model's operations is tested against it, the reports joined and recorded with the key") {
    val (sqlite, memory) = (Tables.sqlite(Projects.rooms), Tables.inMemory(Projects.rooms))
    (modelled(sqlite), modelled(memory), modelled(sqlite ++ memory)).tupled.map { (o, w, both) =>
      val reports = List(o, w, both).map(_._1.toMap.getOrElse(model, fail("not tested")))
      val joined = reports(2)
      assertEquals(reports.map(r => (r.outcome, r.against)).distinct, List((Outcome.Passed,
        Against.Model(model, storedBookings.name))))
      assertEquals(joined.count, Count(reports(0).count.asked + reports(1).count.asked,
        reports(0).count.tried + reports(1).count.tried))
      assertEquals(both._2.inputs.recorded.tests.get(model), Some((TestKeys.of(both._2, model), joined)))
      assertEquals(both._2.tested(model), Some(joined))
    }
  }

  test("a model check is reported by its model; none where no Scala is given") {
    assertEquals(Tables.sqlite(Projects.rooms).map(_.node), List(model))
    assertEquals(Tables.sqlite(Projects.elaborated(Steps.steps)).map(_.node), Nil)
  }

  test("a model's Scala breaking the model reddens each node resting on it, with no onlyCodeChanges assumption") {
    val e = Projects.elaborated(rooms.Forgetting.kb)
    val store = NodeId("storeWhenFree")
    for
      p   <- Projects.inMemory(Map.empty)
      a   <- Projects.analysed(p, e, Nil)
      out <- TestProgram[IO](p.files, RunCode.inline[IO], ModelCheck.of[IO](Semantics(e), e.theory))(a, None)
    yield
      def unproven(on: frflow.project.pipeline.Analysis) = on.subjects.get(store).toList.flatMap(_.proof.unproven)
      assert(unproven(a).contains(Unproven.NotTested), unproven(a))
      val report = out._2.testedModel(storedBookings.name)
      assert(report.exists(_.failure.nonEmpty), report)
      assert(unproven(out._2).contains(Unproven.Tests), unproven(out._2))
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
