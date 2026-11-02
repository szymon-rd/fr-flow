import FrFlowGen.Sharing.Whole.Spec

/-! Each of the purpose's Declarations has a meaning meeting what is said of it, the code's words standing in it:
what it says, read as its definition. And what the run is trusted to keep to holds of some run (owner §39): of the
run with no event yet, the clock never went back and housekeeping was never late, whenever the service started. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.Whole.Proofs
open Sharing

theorem consistent_0 : Obl.consistent_0 := by
  unfold Obl.consistent_0 Sharing.permission.claim
  exact ⟨_, fun _ _ _ _ => rfl⟩

theorem consistent_1 : Obl.consistent_1 := by
  unfold Obl.consistent_1 Sharing.whoMayEdit.claim
  exact ⟨_, fun _ _ _ _ => rfl⟩

theorem consistent_2 : Obl.consistent_2 := by
  unfold Obl.consistent_2 Sharing.whatIsTrashed.claim
  exact ⟨_, fun _ _ => rfl⟩

theorem consistent_3 : Obl.consistent_3 := by
  unfold Obl.consistent_3
  refine ⟨[], 0, ?_, ?_⟩ <;> intro pre e post h <;> simp at h

end Sharing.Whole.Proofs
