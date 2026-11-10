import FrFlowGen.Payments.ownerCanPay.Spec
import Proofs.Payments.Lemmas

/-! Authored proofs of the obligations of ownerCanPay. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Payments.ownerCanPay.Proofs
open Payments.ownerCanPay

theorem impl : Obl.impl := by
  intro hA p world hd
  have a := hA p world hd
  revert a
  generalize Payments.paying_run p world = res
  obtain ⟨result, after⟩ := res
  intro a hp
  have e : after.books = Payments.applied world.books p := a hp
  rw [e]
  exact Payments.Lemmas.applied_made _ _ hd hp

end Payments.ownerCanPay.Proofs
