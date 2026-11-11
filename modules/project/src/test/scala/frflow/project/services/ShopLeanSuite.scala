package frflow.project.services

import frflow.eval.run.OnCode
import frflow.project.{Live, Ported, Projects}
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.ObligationStatus
import scala.annotation.experimental
import scala.concurrent.duration.*
import shop.ShopExamples

/** The shop (`examples/shop`), checked by Lean end to end: the stores' contracts are proven of the `def`s printed
  * from their methods, the services' from the stores', and the checkout's from its services' (alone) and from the
  * stores' (among other calls); its examples, the race for the last unit among them, hold in Lean too.
  */
@experimental class ShopLeanSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  private val proofs = List("Lemmas", "Whole", "chargeKeepsSolvent", "putBackKeepsStocked", "doneChargePays",
    "confirmedIsPaid", "refusedLeavesNothing", "placedAgainIsDuplicate", "placedAgainChangesNothing",
    "neverOversold", "neverOverdrawn", "chargedOnce", "duplicateDoesNothing", "leavesOthersUndisturbed")
    .map(n => n -> Ported.proof("shop", "Shop", n))

  test("every claim of the shop is proven, and its examples hold in Lean".tag(Live)) {
    val examples = ShopExamples().elaborated.fold(e => throw AssertionError(e.toString), identity)
    Ported.run(Projects.elaborated(shop.shop), examples, Ported.Lean(proofs, Nil, None), Nil).map { r =>
      assertEquals(Ported.unproven(r.analysis), Map.empty, Ported.table(r.analysis))
      assertEquals(r.analysis.computed.examples.map(_._2).distinct, List(OnCode.Holds))
      // An example is shown by FrFlow's automation, or proven by hand (`Proofs/Shop/Whole.lean`).
      val held = Set[ObligationStatus](ObligationStatus.Shown, ObligationStatus.Proven)
      examples.foreach(e => assert(r.analysis.wholeCheck.flatMap(_.results.find(_.name ==
        ObligationName.Example(e.of, e.at))).exists(x => held(x.status)), e.name))
    }
  }
