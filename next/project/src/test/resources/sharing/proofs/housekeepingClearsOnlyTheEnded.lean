import FrFlowGen.Sharing.housekeepingClearsOnlyTheEnded.Spec

/-! What tidying keeps is tidyContract's: a share it drops is not in force or of a document gone, an invitation not
open, a document gone. And what has ended stays ended: each lifetime's end, once passed, stays passed as time goes
on, whatever the lifetimes are. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.housekeepingClearsOnlyTheEnded.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intros
  refine ⟨fun lib t => ⟨⟨fun s hs => ?_, fun i hi => ?_⟩, fun doc hd => ?_⟩, fun t u htu => ⟨⟨?_, ?_⟩, ?_⟩⟩
  all_goals try (simp only [tidyCode, ofGone, List.mem_filter, decide_eq_true_eq, decide_eq_true_iff]; grind)
  · intro s hs hu
    apply hs
    intro e he
    have := hu e he
    omega
  · intro i hi hu
    apply hi
    simp only [isOpenCode] at hu ⊢
    omega
  · intro doc ⟨a, ha, hat⟩
    exact ⟨a, ha, by omega⟩

end Sharing.housekeepingClearsOnlyTheEnded.Proofs
