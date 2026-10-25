import FrFlowGen.Sharing.TrashPurgedOnTime.Spec
import Proofs.Sharing.Lemmas

/-! Authored proofs of the obligations of TrashPurgedOnTime. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Sharing.TrashPurgedOnTime.Proofs
open Sharing.TrashPurgedOnTime

/-- By induction over the run (`FrFlow.always_when`), housekeeping last ran at most two minutes ago,
and every document in the trash went there less than 30 days before that run. A request puts documents in the trash
only now, or keeps a time the library held (recording and announcing it touch only the log and the outbox);
housekeeping keeps only documents not gone, and when it changes nothing none is gone; delivery touches only the outbox;
a wait keeps within two minutes of the last run (HousekeepingOnTime) and never goes back (ClockNeverGoesBack). -/
theorem complete : Obl.complete := by
  unfold Obl.complete
  intro events startedAt announce record inForce isOpen gone isPending reminderDue warn chase forget tidy housekeep hR hA _ hG hC hH
  have hR' : ∀ l t c, record l t c = { l with log := l.log ++ [Entry.mk (l.log.length : Int) t c] } := fun l t c => hR l t c
  have hA' : ∀ l b r e, announce l b r e = { l with outbox := l.outbox ++ Notifications.noticesOf b r e } := fun l b r e => hA l b r e
  unfold Sharing.TrashPurgedOnTime.claim
  have hK : (0 : Int) < Sharing.trashKeeps := by simp [Sharing.trashKeeps]
  have hW : (0 : Int) ≤ Sharing.housekeepingWithin := by simp [Sharing.housekeepingWithin]
  have goneIs : ∀ doc t, gone doc t ↔ (match doc.trashed with | some at_ => at_ + Sharing.trashKeeps ≤ t | none => False) := by
    intro doc t
    have := hG doc t
    simp only [Sharing.GoneContract.post] at this
    rw [this]
    cases doc.trashed <;> simp
  let ok : Moment → Event → Prop := fun m e => match e with
    | Event.Waited d => 0 ≤ d ∧ m.now + d ≤ m.tidied + Sharing.housekeepingWithin
    | _ => True
  let inv : Moment → Prop := fun m => m.tidied ≤ m.now ∧ m.now ≤ m.tidied + Sharing.housekeepingWithin ∧
    ∀ doc ∈ m.library.documents, (match doc.trashed with | some at_ => m.tidied < at_ + Sharing.trashKeeps | none => True)
  let step := fun m e => Sharing.Run.step announce record (Sharing.mayEdit inForce Sharing.reaches Sharing.covers) Sharing.ownedBy isOpen
    gone isPending reminderDue inForce m e
  have notGone : ∀ (m : Moment) doc, ¬ gone doc m.now →
      (match doc.trashed with | some at_ => m.now < at_ + Sharing.trashKeeps | none => True) := by
    intro m doc hn
    rw [goneIs] at hn
    cases h : doc.trashed with
    | none => trivial
    | some at_ => simp only [h] at hn ⊢; omega
  have kept : ∀ m e, inv m → ok m e → inv (step m e) := by
    intro m e ⟨h1, h2, h3⟩ he
    cases e with
    | Asked r =>
      simp only [inv, step, Sharing.Run.step]
      refine ⟨h1, h2, fun doc hd => ?_⟩
      rw [Sharing.Lemmas.served_eq _ _ hR' hA'] at hd
      split at hd
      · rcases Sharing.Lemmas.answered_documents _ _ _ _ _ m.library m.now r doc hd with h | h | ⟨x, hx, h⟩
        · rw [h]; trivial
        · rw [h]; simp only; omega
        · have := h3 x hx; rw [h] at this; exact this
      · exact h3 doc hd
    | Housekept =>
      simp only [inv, step, Sharing.Run.step]
      refine ⟨Int.le_refl _, by omega, fun doc hd => ?_⟩
      rw [Sharing.Lemmas.housekept_eq _ hR'] at hd
      split at hd
      · simp only [Sharing.Notifications.warnCode, Sharing.Audit.forgetCode, Sharing.AccessRequests.chaseCode, Sharing.Housekeeping.tidyCode, List.mem_filter, decide_eq_true_eq] at hd
        exact notGone m doc hd.2
      · next hn =>
        have hd' : doc ∈ (Sharing.Notifications.warnCode (Sharing.AccessRequests.chaseCode isPending reminderDue (Sharing.Audit.forgetCode (Sharing.Housekeeping.tidyCode gone inForce isOpen m.library m.now) m.now) m.now) m.now).documents := by
          rw [Classical.not_not.mp hn]; exact hd
        simp only [Sharing.Notifications.warnCode, Sharing.Audit.forgetCode, Sharing.AccessRequests.chaseCode, Sharing.Housekeeping.tidyCode, List.mem_filter, decide_eq_true_eq] at hd'
        exact notGone m doc hd'.2
    | Delivered =>
      simp only [inv, step, Sharing.Run.step]
      split <;> exact ⟨h1, h2, h3⟩
    | Waited d =>
      simp only [ok] at he
      simp only [inv, step, Sharing.Run.step]
      refine ⟨by omega, by omega, fun doc hd => ?_⟩
      exact h3 doc hd
  have h := FrFlow.always_when step ok inv
    (Moment.mk (Library.mk [] [] [] [] [] [] [] []) startedAt startedAt []) ⟨Int.le_refl _, by simp only; omega, by simp⟩ kept events
    (fun pre e post hp => by
      have hc := hC pre post e hp
      have hh := hH pre post e hp
      cases e with
      | Waited d => exact ⟨hc, hh⟩
      | _ => trivial)
  simp only [step] at h
  obtain ⟨_, h2, h3⟩ := h
  intro doc hd
  simp only [Sharing.Run.after] at hd ⊢
  have := h3 doc hd
  cases ht : doc.trashed with
  | none => trivial
  | some at_ => simp only [ht] at this ⊢; omega

end Sharing.TrashPurgedOnTime.Proofs
