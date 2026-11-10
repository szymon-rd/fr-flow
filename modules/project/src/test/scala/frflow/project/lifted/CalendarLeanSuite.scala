package frflow.project.lifted

import frflow.core.name.NodeId
import frflow.eval.lifted.Calendar
import frflow.project.{Live, Ported, Projects}
import scala.concurrent.duration.*

/** Plain Scala read by `lifted`, checked by Lean end to end: the calendar's decision, written as the Scala it runs
  * as, is proven to meet its claim over start and end times (`impl`, of the `def` printed from the term read), and
  * that claim gives the one over moments (`complete`, rooms' own proof of the step).
  */
class CalendarLeanSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  test("the calendar's plain Scala is proven to meet its claims".tag(Live)) {
    val proofs = List("grantWhenFree" -> Ported.resource("lifted/grantWhenFree.lean"))
    Ported.run(Projects.elaborated(Calendar.model), Nil, Ported.Lean(proofs, Nil, None), Nil).map { r =>
      List("grantWhenFree", "grantWhenNoOverlap").foreach(n =>
        assertEquals(Ported.row(r.analysis, NodeId(n)).take(3).drop(1), List("proven", "proven"),
          s"$n\n${Ported.table(r.analysis)}"))
    }
  }
