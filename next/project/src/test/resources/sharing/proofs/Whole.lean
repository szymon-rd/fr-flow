import FrFlowGen.Sharing.Whole.Spec

/-! What the run is trusted to keep to holds of some run (owner §39): of the run with no event yet, the clock never
went back and housekeeping was never late, whenever the service started. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.Whole.Proofs
open Sharing

theorem consistent_0 : Obl.consistent_0 := by
  unfold Obl.consistent_0
  refine ⟨[], 0, ?_, ?_⟩ <;> intro pre e post h <;> simp at h

end Sharing.Whole.Proofs
