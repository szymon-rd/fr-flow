package frflow.project.program

import frflow.core.name.NodeId
import frflow.decision.review.ReviewState
import frflow.project.Projects
import frflow.project.port.Records
import frflow.project.report.NodeReport
import frflow.wire.file.Files
import frflow.wire.snapshot.{Body, Snapshot}

/** `status`, `export`, `show` and `review` on rooms in memory: the Lean and the snapshot written, the snapshot
  * reading back in decision order, each node as the review reads it; a node the model does not have shows nothing.
  */
class StatusProgramSuite extends munit.CatsEffectSuite:
  test("status writes the Lean and the snapshot, and gives the review: every node proposed, in decision order") {
    for
      p      <- Projects.inMemory(Map.empty)
      a      <- Projects.analysed(p, Projects.rooms, Projects.roomsExamples)
      review <- StatusProgram(p.files, "lean")(a)
      held   <- p.files.all
    yield
      assertEquals(review.nodes.map(_.subject.id), a.subjects.inOrder.map(_.id))
      assertEquals(review.nodes.map(_.standing.state).distinct, List(ReviewState.Proposed))
      assert(a.modules.forall(m => held.contains(m.name.file)))
      val snapshot = held.get(Records.path(Snapshot.format)).map(Files.read(Snapshot.format, _))
      assertEquals(snapshot.flatMap(_.toOption).map(_.nodes.map(_.header.id)),
        Some(a.subjects.inOrder.map(_.id.value)))
  }

  test("the snapshot says how each claim is checked, the Definition it is a call of, and its examples as checked") {
    for
      p    <- Projects.inMemory(Map.empty)
      a    <- Projects.analysed(p, Projects.rooms, Projects.roomsExamples)
      text <- ExportProgram(p.files)(a)
    yield
      val s = Files.read(Snapshot.format, text).fold(e => fail(e.toString), identity)
      val grant = s.nodes.find(_.header.id == "grantWhenNoOverlap").map(_.body)
      assert(grant.exists {
        case Body.Stated(checking, call, _, _) => call.contains("granted") && checking.nonEmpty
        case _                                 => false
      }, grant)
      assertEquals(s.examples.map(_.onCode), List("holds", "holds"))
  }

  test("show: a node as the review reads it, with its check and tests when current; a node not in the model, none") {
    for
      p <- Projects.inMemory(Map.empty)
      a <- Projects.analysed(p, Projects.rooms, Nil)
    yield
      val shown = NodeReport.of(a, NodeId("grantWhenFree"))
      assertEquals(shown.map(r => (r.reviewed.subject.id, r.recent.check, r.recent.tests, r.binding)),
        Some((NodeId("grantWhenFree"), None, None, None)))
      assertEquals(NodeReport.of(a, NodeId("gone")), None)
  }
