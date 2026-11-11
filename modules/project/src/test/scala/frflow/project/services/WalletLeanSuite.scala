package frflow.project.services

import frflow.eval.run.OnCode
import frflow.project.{Live, Ported, Projects}
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.ObligationStatus
import scala.annotation.experimental
import scala.concurrent.duration.*
import wallet.WalletExamples

/** The wallet (`examples/wallet`), checked by Lean end to end: the ledger's contracts are proven of the `def`s
  * printed from its methods, the transfer service's (among other calls and alone) from the ledger's, and the
  * examples, the schedule that overdraws an account under the hasty service among them, are decided by Lean too.
  */
@experimental class WalletLeanSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  private val proofs = List("Lemmas", "Whole", "moveKeepsSolvent", "carriedOutOnce", "sentAgainChangesNothing",
    "leavesOthersUndisturbed", "postsOnlyOnceClaimed", "hastyIsSafeAlone", "hastyAnswersDuplicates")
    .map(n => n -> Ported.proof("wallet", "Wallet", n))

  test("every claim of the wallet is proven, and its examples hold in Lean".tag(Live)) {
    val examples = WalletExamples().elaborated.fold(e => throw AssertionError(e.toString), identity)
    Ported.run(Projects.elaborated(wallet.wallet), examples, Ported.Lean(proofs, Nil, None), Nil).map { r =>
      assertEquals(Ported.unproven(r.analysis), Map.empty, Ported.table(r.analysis))
      assertEquals(r.analysis.computed.examples.map(_._2).distinct, List(OnCode.Holds))
      // An example is shown by FrFlow's automation, or proven by hand (`Proofs/Wallet/Whole.lean`).
      val held = Set[ObligationStatus](ObligationStatus.Shown, ObligationStatus.Proven)
      examples.foreach(e => assert(r.analysis.wholeCheck.flatMap(_.results.find(_.name ==
        ObligationName.Example(e.of, e.at))).exists(x => held(x.status)), e.name))
    }
  }
