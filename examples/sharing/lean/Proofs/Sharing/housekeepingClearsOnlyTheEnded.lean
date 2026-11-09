import FrFlowGen.Sharing.housekeepingClearsOnlyTheEnded.Spec
import Proofs.Sharing.Lemmas

/-! What tidying keeps is tidyContract's: a share it drops is not in force or of a document gone, an invitation
not open, a document gone. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.housekeepingClearsOnlyTheEnded.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro _ lib t
  simp only [clearsOnlyTheEnded, endedShare]
  refine ⟨⟨fun s hs => ?_, fun i hi => ?_⟩, fun doc hd => ?_⟩
  all_goals (simp only [tidyCode, ofGone, List.mem_filter, decide_eq_true_eq, decide_eq_true_iff]; grind)

end Sharing.housekeepingClearsOnlyTheEnded.Proofs
