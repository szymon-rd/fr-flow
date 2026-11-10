import FrFlowGen.Payments.othersUntouched.Spec
import Proofs.Payments.Lemmas

/-! Authored proofs of the obligations of othersUntouched. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Payments.othersUntouched.Proofs
open Payments.othersUntouched

theorem impl : Obl.impl := by
  intro hA hR p i world hd
  have a := hA p world hd
  have r := hR p world hd
  revert a r
  generalize Payments.paying_run p world = res
  obtain ⟨result, after⟩ := res
  intro a r hi
  by_cases hp : Payments.payable world.books p
  · have e : after.books = Payments.applied world.books p := a hp
    show Payments.balanceOf after.books i = Payments.balanceOf world.books i
    rw [e]
    exact Payments.Lemmas.applied_other _ _ i hi.1 hi.2
  · have e : after.books = world.books := r hp
    show Payments.balanceOf after.books i = Payments.balanceOf world.books i
    rw [e]

end Payments.othersUntouched.Proofs
