package rooms

import frflow.project.{Live, Ported, Projects, Tables}
import frflow.project.Ported.Lean
import frflow.proof.audit.Completeness
import scala.concurrent.duration.*

/** Rooms checked whole: by Lean and by tests (the calendar on generated cases, the table against its model on
  * generated runs), every node proven or tested. The seeded bugs are the README's changes (`WalkthroughSuite`).
  */
class PortSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 40.minutes

  /** The developer's proofs (`examples/rooms/lean/Proofs/Rooms`): the code's steps, the calendar's, what the table
    * keeps.
    */
  private val proofs: List[String] =
    List("Lemmas", "storeWhenFree", "answerWhenFree", "grantWhenFree", "neverOverlap", "roomBookingsApart")
  private val lean = Lean(proofs.map(n => n -> Ported.proof("rooms", "Rooms", n)), Nil, None)

  test("checked by Lean and tested: every node is proven or tested, and the theory's own check is recorded".tag(Live)) {
    Ported.run(Projects.rooms, Projects.roomsExamples, lean, Tables.sqlite(Projects.rooms)).map { r =>
      val a = r.analysis
      assertEquals(Completeness.of(a.decided, a.modules), Nil)
      assertEquals(Ported.unproven(a), Map.empty[String, List[String]])
      assert(a.wholeCheck.isDefined, "the theory's own check is recorded")
    }
  }
