import FrFlowGen.Wallet.hastyAnswersDuplicates.Spec
import Proofs.Wallet.Lemmas

/-! The hasty transfer's first step, with no other call before it, sees the request claimed. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Wallet.hastyAnswersDuplicates.Proofs
open Wallet Wallet.Lemmas

theorem impl : Obl.impl := by
  intro books between t _ hseen
  unfold hastyAmongOthersCode
  simp only [hseen, ite_true]

end Wallet.hastyAnswersDuplicates.Proofs
