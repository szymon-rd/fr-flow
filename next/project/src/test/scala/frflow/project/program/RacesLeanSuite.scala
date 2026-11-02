package frflow.project.program

import frflow.core.name.NodeId
import frflow.project.{Live, Ported, Projects}
import scala.concurrent.duration.*
import frflow.eval.flow.RaceProbe

/** The step 13 review's race probe (B1), checked by Lean: a race is read as the winner after the loser's steps until
  * the scheduler cancels it, what they did kept. So the claim that the box is untouched when the sleep wins, false of
  * production's run (`whole.RaceProbeSuite`), stays unproven; the one that both adds landed when they win is proven,
  * whatever the cancelled sleep did: a racing program's run with both choices of its winner.
  */
class RacesLeanSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  test("the review's probe: when the sleep wins, the box may have changed, so the claim it did not stays unproven"
    .tag(Live)) {
    Ported.run(Projects.elaborated(RaceProbe.knowledge), Nil, Ported.Lean(Nil, Nil, None), Nil).map { r =>
      assertEquals(Ported.row(r.analysis, NodeId("limitWinsUntouched")).take(3), List("claim", "open", "open"),
        Ported.table(r.analysis))
      assert(Ported.unproven(r.analysis).contains("limitWinsUntouched"), Ported.table(r.analysis))
    }
  }

  test("the same race: when the adds win, both landed, whatever the cancelled sleep did: proven".tag(Live)) {
    Ported.run(Projects.elaborated(RaceProbe.winning), Nil, Ported.Lean(Nil, Nil, None), Nil).map { r =>
      assertEquals(Ported.row(r.analysis, NodeId("addsWinAddBoth")).take(3), List("claim", "proven", "proven"),
        Ported.table(r.analysis))
    }
  }
