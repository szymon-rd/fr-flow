import FrFlowGen.Payments.onlyOwnerPays.Spec
import Proofs.Payments.Lemmas

/-! Authored proofs of the obligations of onlyOwnerPays. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Payments.onlyOwnerPays.Proofs
open Payments.onlyOwnerPays

theorem impl : Obl.impl := by
  intro hR p world hd
  have r := hR p world hd
  revert r
  generalize Payments.paying_run p world = res
  obtain ⟨result, after⟩ := res
  intro r hno
  exact r (fun hp => hno hp.1.1.1.1.1)

end Payments.onlyOwnerPays.Proofs
