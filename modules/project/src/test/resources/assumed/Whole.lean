import FrFlowGen.Registers.Whole.Spec

/-! What is assumed of the index, and what the program putting a number once is claimed to do, hold together
(owner §39): an index answering from the register itself, leaving it as it was. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Registers.Whole.Proofs

theorem consistent_0 : Obl.consistent_0 := by
  refine ⟨fun n => (do let xs ← get; pure (n ∈ xs) : StateM (List Int) Prop), ?_⟩
  frflow_auto

end Registers.Whole.Proofs
