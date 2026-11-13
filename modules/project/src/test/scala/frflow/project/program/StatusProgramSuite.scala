package frflow.project.program

import frflow.proof.rocq.RocqProject
import frflow.decision.review.ReviewState
import frflow.project.Projects
import frflow.project.port.Records
import frflow.wire.file.Files
import frflow.wire.snapshot.{Body, Snapshot}

/** `status` and `export` on rooms in memory: the Rocq and the snapshot written, the snapshot reading back in
  * decision order.
  */
class StatusProgramSuite extends munit.CatsEffectSuite:
  test("status writes the Rocq and the snapshot: every node proposed, in decision order") {
    for
      p      <- Projects.inMemory(Map.empty)
      a      <- Projects.analysed(p, Projects.rooms, Projects.roomsExamples)
      _      <- StatusProgram(p.files)(a)
      held   <- p.files.all
    yield
      assertEquals(a.reading.standings.values.map(_.state).toList.distinct.filterNot(_ == ReviewState.Proposed), Nil)
      assert(a.modules.forall(m => held.contains(RocqProject.path(m.name))))
      val snapshot = held.get(Records.path(Snapshot.format)).map(Files.read(Snapshot.format, _))
      assertEquals(snapshot.flatMap(_.toOption).map(_.nodes.map(_.header.id)),
        Some(a.subjects.inOrder.map(_.id.value)))
  }

  test("the snapshot says how each claim is checked, the code it is proven of, and its examples as checked") {
    for
      p    <- Projects.inMemory(Map.empty)
      a    <- Projects.analysed(p, Projects.rooms, Projects.roomsExamples)
      text <- ExportProgram(p.files)(a)
    yield
      val s = Files.read(Snapshot.format, text).fold(e => fail(e.toString), identity)
      val grant = s.nodes.find(_.header.id == "answerWhenNoOverlap").map(_.body)
      assert(grant.exists {
        case Body.Stated(checking, _, code, _) =>
          checking.nonEmpty && code.exists(_.proven.contains("storedBookings_book"))
        case _                                 => false
      }, grant)
      assertEquals(s.examples.map(_.onCode), List("holds", "holds"))
  }
