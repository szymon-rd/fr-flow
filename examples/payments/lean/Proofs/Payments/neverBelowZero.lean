import FrFlowGen.Payments.neverBelowZero.Spec
import Proofs.Payments.Lemmas

/-! Authored proofs of the obligations of neverBelowZero. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Payments.neverBelowZero.Proofs
open Payments.neverBelowZero

theorem impl : Obl.impl := by
  intro hA hR p world hd
  have a := hA p world hd
  have r := hR p world hd
  revert a r
  generalize Payments.paying_run p world = res
  obtain ⟨result, after⟩ := res
  intro a r hn
  by_cases hp : Payments.payable world.books p
  · have e : after.books = Payments.applied world.books p := a hp
    show Payments.noneNegative after.books
    rw [e]
    exact Payments.Lemmas.applied_nonneg _ _ hn hd hp
  · have e : after.books = world.books := r hp
    show Payments.noneNegative after.books
    rw [e]
    exact hn

end Payments.neverBelowZero.Proofs
