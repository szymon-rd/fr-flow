import FrFlowGen.Rebac.ChecksExactly.Spec

/-! Authored proofs of the obligations of ChecksExactly. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Rebac.ChecksExactly.Proofs
open Rebac.ChecksExactly

/-- The check's resolution through the two indexes gives what the tuples of the version give: the indexes read exactly
what `stored` and `rulesOf` say (StoreIndex, SchemaIndex), so resolution and the derivation take the same steps; by
induction on the depth. -/
theorem complete : Obl.complete := by
  unfold Obl.complete
  frflow_intro
  simp only [frflow_defs] at *
  have ht : ∀ v o, tuplesOf v o = stored writes v o := by
    intro v o; rw [h_StoreIndex]; simp only [frflow_defs]
  have hr : ∀ k r, rulesFor k r = rulesOf schema k r := by
    intro k r; rw [h_SchemaIndex]; simp only [frflow_defs]
  intro q v
  rw [h_CheckContract]
  suffices h : ∀ (fuel : List Unit) (o : Obj) (r : String),
      resolve rulesFor tuplesOf fuel v o r q.person = holds (stored writes) schema fuel v o r q.person from h _ _ _
  intro fuel
  induction fuel with
  | nil => intro o r; simp [resolve, holds]
  | cons _ rest ih => intro o r; simp only [resolve, holds, ht, hr, ih]; rfl

end Rebac.ChecksExactly.Proofs
