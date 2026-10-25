import FrFlowGen.Sharing.TrashPurgedOnTime.Spec
import Proofs.Sharing.Lemmas

/-! Authored proofs of the obligations of TrashPurgedOnTime. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Sharing.TrashPurgedOnTime.Proofs
open Sharing.TrashPurgedOnTime

/-- Never before: tidying keeps every document not gone, and a document gone has been 30 days in the trash
(GoneContract). After: by induction over the run (`FrFlow.always_when`), housekeeping last ran at most two minutes ago,
and every document in the trash went there less than 30 days before that run. A request puts documents in the trash
only now, or keeps a time the library held; housekeeping keeps only documents not gone; a wait keeps within two
minutes of the last run (HousekeepingOnTime) and never goes back (ClockNeverGoesBack). -/
theorem complete : Obl.complete := by
  unfold Obl.complete
  intro events gone inForce isOpen startedAt tidy housekeep _ hG hC hH
  unfold Sharing.TrashPurgedOnTime.claim
  have hK : (0 : Int) < Sharing.trashKeeps := by simp [Sharing.trashKeeps]
  have hW : (0 : Int) ≤ Sharing.housekeepingWithin := by simp [Sharing.housekeepingWithin]
  have goneIs : ∀ doc t, gone doc t ↔ (match doc.trashed with | some at_ => at_ + Sharing.trashKeeps ≤ t | none => False) := by
    intro doc t
    have := hG doc t
    simp only [Sharing.GoneContract.post] at this
    rw [this]
    cases doc.trashed <;> simp
  refine ⟨fun lib t doc hd => ?_, ?_⟩
  · by_cases g : gone doc t
    · right; exact (goneIs doc t).1 g
    · left
      simp only [Sharing.Housekeeping.tidyCode, List.mem_filter, decide_eq_true_eq]
      exact ⟨hd, g⟩
  · let ok : Moment → Event → Prop := fun m e => match e with
      | Event.Waited d => 0 ≤ d ∧ m.now + d ≤ m.tidied + Sharing.housekeepingWithin
      | _ => True
    let inv : Moment → Prop := fun m => m.tidied ≤ m.now ∧ m.now ≤ m.tidied + Sharing.housekeepingWithin ∧
      ∀ doc ∈ m.library.documents, (match doc.trashed with | some at_ => m.tidied < at_ + Sharing.trashKeeps | none => True)
    have kept : ∀ m e, inv m → ok m e →
        inv (Sharing.Run.step (Sharing.mayEdit inForce Sharing.reaches Sharing.covers) isOpen gone inForce m e) := by
      intro m e ⟨h1, h2, h3⟩ he
      cases e with
      | Asked r =>
        simp only [inv, Sharing.Run.step]
        refine ⟨h1, h2, fun doc hd => ?_⟩
        rcases Sharing.Lemmas.answered_documents _ _ _ _ _ r doc hd with h | h | ⟨x, hx, h⟩
        · rw [h]; trivial
        · rw [h]; simp only; omega
        · have := h3 x hx; rw [h] at this; exact this
      | Housekept =>
        simp only [inv, Sharing.Run.step, Sharing.Housekeeping.tidyCode, List.mem_filter, decide_eq_true_eq]
        refine ⟨Int.le_refl _, by omega, fun doc hd => ?_⟩
        have := hd.2
        rw [goneIs] at this
        cases h : doc.trashed with
        | none => trivial
        | some at_ => simp only [h] at this ⊢; omega
      | Waited d =>
        simp only [ok] at he
        simp only [inv, Sharing.Run.step]
        refine ⟨by omega, by omega, fun doc hd => ?_⟩
        have := h3 doc hd
        cases h : doc.trashed with
        | none => trivial
        | some at_ => simp only [h] at this ⊢; omega
    have h := FrFlow.always_when (fun m e => Sharing.Run.step (Sharing.mayEdit inForce Sharing.reaches Sharing.covers) isOpen gone inForce m e)
      ok inv (Moment.mk (Library.mk [] [] [] [] []) startedAt startedAt) ⟨Int.le_refl _, by simp only; omega, by simp⟩ kept events
      (fun pre e post hp => by
        have hc := hC pre post e hp
        have hh := hH pre post e hp
        cases e with
        | Waited d => exact ⟨hc, hh⟩
        | _ => trivial)
    obtain ⟨_, h2, h3⟩ := h
    intro doc hd
    simp only [Sharing.Run.after] at hd ⊢
    have := h3 doc hd
    cases ht : doc.trashed with
    | none => trivial
    | some at_ => simp only [ht] at this ⊢; omega

end Sharing.TrashPurgedOnTime.Proofs
