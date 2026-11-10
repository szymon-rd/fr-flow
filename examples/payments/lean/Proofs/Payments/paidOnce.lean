import FrFlowGen.Payments.paidOnce.Spec
import Proofs.Payments.Lemmas

/-! Authored proofs of the obligations of paidOnce. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Payments.paidOnce.Proofs
open Payments.paidOnce

theorem impl : Obl.impl := by
  intro hR p world hd
  have r := hR p world hd
  revert r
  generalize Payments.paying_run p world = res
  obtain ⟨result, after⟩ := res
  intro r hpaid
  exact r (fun hp => hp.2 hpaid)

end Payments.paidOnce.Proofs
