import FrFlowGen.Sharing.Whole.Spec

/-! Each of the purpose's Declarations has a meaning meeting what is said of it, the code's words standing in it:
what it says, read as its definition. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.Whole.Proofs
open Sharing

theorem consistent_0 : Obl.consistent_0 := by
  unfold Obl.consistent_0 Sharing.permission.claim
  exact ⟨_, fun _ _ _ _ _ => rfl⟩

theorem consistent_1 : Obl.consistent_1 := by
  unfold Obl.consistent_1 Sharing.whoMayEdit.claim
  exact ⟨_, fun _ _ _ _ _ => rfl⟩

theorem consistent_2 : Obl.consistent_2 := by
  unfold Obl.consistent_2 Sharing.whatIsTrashed.claim
  exact ⟨_, fun _ _ _ => rfl⟩

end Sharing.Whole.Proofs
