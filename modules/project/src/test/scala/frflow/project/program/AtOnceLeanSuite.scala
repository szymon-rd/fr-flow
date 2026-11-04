package frflow.project.program

import frflow.core.name.NodeId
import frflow.eval.flow.InterferenceProbe
import frflow.project.{Live, Ported, Projects}
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.ObligationStatus
import scala.concurrent.duration.*

/** The step 13 re-review's probes (RB1, RB2), checked by Lean: sides at once are read in turn only where each step
  * of one commutes with each step of the other on the models they share (`commute_i`). A race's set beside a read of
  * the same number, and two bumps at once, each a read then a set, do not commute, so the claims read in turn would
  * prove, false of production's runs (`InterferenceProbeSuite`), stay unproven; steps on models apart ask nothing and
  * are proven. The bumps' branches give the unit: their pair builds (RS2).
  */
class AtOnceLeanSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  private def checked(kb: frflow.FrModel, node: String) =
    Ported.run(Projects.elaborated(kb), Nil, Ported.Lean(Nil, Nil, None), Nil).map { r =>
      val results = r.analysis.current(NodeId(node)).toList.flatMap(_.results)
      (Ported.row(r.analysis, NodeId(node)).take(3), results.collect {
        case x if x.name.isInstanceOf[ObligationName.Commute] => x.name -> x.status
      }, Ported.table(r.analysis))
    }

  test("RB1: when the set wins, the copy may have read the new number, so the claim it did not stays unproven"
    .tag(Live)) {
    checked(InterferenceProbe.raced, "copiesOld").map { (row, commutes, table) =>
      assertEquals(row, List("claim", "open", "open"), table)
      assertEquals(commutes, List(ObligationName.Commute(0) -> ObligationStatus.Open), table)
    }
  }

  test("RB2: two bumps at once may lose one, so the claim that they add two stays unproven; two reads commute"
    .tag(Live)) {
    checked(InterferenceProbe.bumped, "upByTwo").map { (row, commutes, table) =>
      assertEquals(row, List("claim", "open", "open"), table)
      assertEquals(commutes, List(ObligationStatus.Proven, ObligationStatus.Open, ObligationStatus.Open,
        ObligationStatus.Open).zipWithIndex.map((s, i) => ObligationName.Commute(i) -> s), table)
    }
  }

  test("steps at once on models apart commute by construction: nothing is asked, and the claim is proven".tag(Live)) {
    checked(InterferenceProbe.separate, "bothSet").map { (row, commutes, table) =>
      assertEquals((row, commutes), (List("claim", "proven", "proven"), Nil), table)
    }
  }
