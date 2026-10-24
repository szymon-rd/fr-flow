import FrFlowGen.Rebac.CheckContract.Spec

/-! Authored proofs of the obligations of CheckContract. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Rebac.CheckContract.Proofs
open Rebac.CheckContract

/-- The service's cheap check follows from the contract: a check resolved to yes took a rule of the relation, so the
schema index gives it some. -/
theorem check : Obl.check := by
  unfold Obl.check
  intro levels rulesFor tuplesOf q v answer hpost
  simp only [Rebac.CheckContract.post, Rebac.CheckContract.runCheck] at *
  intro ha hnil
  have hr := hpost.mp ha
  cases levels with
  | nil => simp [Rebac.resolve] at hr
  | cons _ rest =>
    simp only [Rebac.resolve] at hr
    obtain ⟨rule, hmem, _⟩ := hr
    simp [hnil] at hmem

end Rebac.CheckContract.Proofs
