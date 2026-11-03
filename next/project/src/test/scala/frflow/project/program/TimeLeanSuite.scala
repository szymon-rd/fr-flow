package frflow.project.program

import frflow.core.name.NodeId
import frflow.eval.flow.Stamps
import frflow.project.{Live, Ported, Projects}
import scala.concurrent.duration.*

/** Time as Cats Effect models it (owner §47), checked by Lean: a rule time passing keeps is proven of the world's own
  * step (`cover_elapse`), a time limit fires only once its time passed, a race lost to a wait took the wait's
  * seconds, and two waits at once take the longer; the bugs time passing finds stay unproven: a rule it breaks, a
  * program relying on its own run taking no time, a time limit claimed never to fire, waits at once said to add up.
  */
class TimeLeanSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  test("what holds as time passes is proven: a rule time keeps, a limit firing late, a wait won, waits at once"
    .tag(Live)) {
    Ported.run(Projects.elaborated(Stamps.kept), Nil, Ported.Lean(Nil, Nil, None), Nil).map { r =>
      List("pastStamps", "stampsTheTime", "firesLate", "waitWins", "waitsAtOnce").foreach(n =>
        assertEquals(Ported.row(r.analysis, NodeId(n)).take(3).drop(1), List("proven", "proven"),
          s"$n\n${Ported.table(r.analysis)}"))
    }
  }

  test(("the bugs time passing finds stay unproven: a rule it breaks, a run taking no time, a limit never firing, " +
      "waits at once adding up").tag(Live)) {
    Ported.run(Projects.elaborated(Stamps.seeded), Nil, Ported.Lean(Nil, Nil, None), Nil).map { r =>
      List("freshStamps", "stampTakesNoTime", "neverGivenUp", "waitsAddUp", "waitWinsLate").foreach(n =>
        assert(Ported.unproven(r.analysis).contains(n), s"$n\n${Ported.table(r.analysis)}"))
    }
  }
