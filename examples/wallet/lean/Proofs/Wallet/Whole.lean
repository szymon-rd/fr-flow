import FrFlowGen.Wallet.Whole.Spec
import Proofs.Wallet.Lemmas

/-! The wallet's examples FrFlow's automation does not decide within an example's budget, each its code's run on
the books and the schedule given: a transfer sent again, and the schedule on which the other call pays Carol from
Alice's account between two steps of the call paying Bob. Under the hasty service the transfer is done and an
account is left overdrawn (`example_WalletExamples_3`, `_4`); under the transfer service it is refused and none is
(`_5`, `_6`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Wallet.Whole.Proofs
open Wallet

theorem example_WalletExamples_1 : Obl.example_WalletExamples_1 := by
  intro _ _ _ _; simp [transferCode, claimCode, moveIfCoveredCode, balance]

theorem example_WalletExamples_3 : Obl.example_WalletExamples_3 := by
  intro _ _; simp [hastyAmongOthersCode, others, undisturbed, solvent, orderly, made, balance]

theorem example_WalletExamples_4 : Obl.example_WalletExamples_4 := by
  intro _ _; simp [hastyAmongOthersCode, others, undisturbed, solvent, orderly, made, balance]

theorem example_WalletExamples_5 : Obl.example_WalletExamples_5 := by
  intro _ _ _ _
  simp [transferAmongOthersCode, claimCode, moveIfCoveredCode, others, undisturbed, solvent, orderly, made, balance]

theorem example_WalletExamples_6 : Obl.example_WalletExamples_6 := by
  intro _ _ _ _
  simp [transferAmongOthersCode, claimCode, moveIfCoveredCode, others, undisturbed, solvent, orderly, made, balance]

end Wallet.Whole.Proofs
