package frflow.project

import frflow.core.name.NodeId
import frflow.eval.flow.Stamps
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

  /** Kept by the schedule, proven by hand (`resources/stamps/proofs`): stamping reads the time and the world's tick
    * moves it before the stamp, so it rests on each stamp being of a time already come.
    */
  private val scheduledProofs = List("freshWhileScheduled").map(n =>
    n -> Ported.resource(s"stamps/proofs/$n.lean"))

  test(("a schedule kept: a rule time passing alone would break holds where the world moves the time only as the " +
      "schedule allows, at the program's tick and between runs").tag(Live)) {
    Ported.run(Projects.elaborated(Stamps.scheduled), Nil, Ported.Lean(scheduledProofs, Nil, None), Nil).map { r =>
      List("freshWhileScheduled", "pastWhileScheduled", "stampsScheduled").foreach(n =>
        assertEquals(Ported.row(r.analysis, NodeId(n)).take(3).drop(1), List("proven", "proven"),
          s"$n\n${Ported.table(r.analysis)}"))
    }
  }
