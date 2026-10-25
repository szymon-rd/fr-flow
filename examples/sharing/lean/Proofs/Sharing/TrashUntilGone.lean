import FrFlowGen.Sharing.TrashUntilGone.Spec
import Proofs.Sharing.Lemmas

/-! Authored proofs of the obligations of TrashUntilGone. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Sharing.TrashUntilGone.Proofs
open Sharing.TrashUntilGone

/-- The operations by their contracts; that a gone document is purged within one period of housekeeping is
TrashPurgedOnTime's deadline, read through GoneContract. -/
theorem complete : Obl.complete := by
  unfold Obl.complete
  frflow_intro
  unfold Sharing.TrashUntilGone.claim
  refine ⟨?_, ?_⟩
  · clear h_TrashPurgedOnTime h_GoneContract
    simp only [frflow_defs] at *
    refine fun lib t by_ d => ⟨fun h => ?_, fun h => ?_⟩
    · rw [h_TrashContract] at h; exact Sharing.Lemmas.changed h
    · rw [h_RestoreContract] at h; exact Sharing.Lemmas.changed h
  · have goneIs : ∀ doc t, gone doc t ↔ (match doc.trashed with | some at_ => at_ + Sharing.trashKeeps ≤ t | none => False) := by
      intro doc t
      have := h_GoneContract doc t
      simp only [Sharing.GoneContract.post] at this
      rw [this]
      cases doc.trashed <;> simp
    have h := h_TrashPurgedOnTime
    unfold Sharing.TrashPurgedOnTime.claim at h
    intro doc hd
    rw [goneIs]
    have := h doc hd
    cases ht : doc.trashed with
    | none => simp
    | some at_ => simp only [ht] at this ⊢; omega

end Sharing.TrashUntilGone.Proofs
