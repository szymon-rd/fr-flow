import FrFlowGen.Sharing.InvitationsLapseOnTime.Spec
import Proofs.Sharing.Lemmas

/-! Authored proofs of the obligations of InvitationsLapseOnTime. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Sharing.InvitationsLapseOnTime.Proofs
open Sharing.InvitationsLapseOnTime

/-- By induction over the run (`FrFlow.always_when`), with the last run of housekeeping in the state: housekeeping last
ran at most two minutes ago, and every invitation pending was sent less than 7 days before it. A request sends
invitations only now (recording and announcing it touch only the log and the outbox); housekeeping keeps only open ones
(IsOpenContract), and when it changes nothing every one is open; delivery touches only the outbox; a wait keeps within two
minutes of the last run (HousekeepingOnTime) and never goes back (ClockNeverGoesBack). -/
theorem complete : Obl.complete := by
  unfold Obl.complete
  intro events startedAt announce record inForce isOpen gone isPending reminderDue warn chase forget tidy housekeep hR hA _ hO hC hH
  have hR' : ∀ l t c, record l t c = { l with log := l.log ++ [Entry.mk (l.log.length : Int) t c] } := fun l t c => hR l t c
  have hA' : ∀ l b r e, announce l b r e = { l with outbox := l.outbox ++ Notifications.noticesOf b r e } := fun l b r e => hA l b r e
  unfold Sharing.InvitationsLapseOnTime.claim
  have hL : (0 : Int) < Sharing.invitationLasts := by simp [Sharing.invitationLasts]
  have hW : (0 : Int) ≤ Sharing.housekeepingWithin := by simp [Sharing.housekeepingWithin]
  have openIs : ∀ i t, isOpen i t ↔ t < i.sent + Sharing.invitationLasts := by
    intro i t; have := hO i t; simp only [Sharing.IsOpenContract.post] at this; rw [this]
  let ok : Moment → Event → Prop := fun m e => match e with
    | Event.Waited d => 0 ≤ d ∧ m.now + d ≤ m.tidied + Sharing.housekeepingWithin
    | _ => True
  let inv : Moment → Prop := fun m => m.tidied ≤ m.now ∧ m.now ≤ m.tidied + Sharing.housekeepingWithin ∧
    ∀ i ∈ m.library.invitations, m.tidied < i.sent + Sharing.invitationLasts
  let step := fun m e => Sharing.Run.step announce record (Sharing.mayEdit inForce Sharing.reaches Sharing.covers) Sharing.ownedBy isOpen
    gone isPending reminderDue inForce m e
  have kept : ∀ m e, inv m → ok m e → inv (step m e) := by
    intro m e ⟨h1, h2, h3⟩ he
    cases e with
    | Asked r =>
      simp only [inv, step, Sharing.Run.step]
      refine ⟨h1, h2, fun i hi => ?_⟩
      rw [Sharing.Lemmas.served_eq _ _ hR' hA'] at hi
      split at hi
      · rcases Sharing.Lemmas.answered_invitations _ _ _ _ _ m.library m.now r i hi with h | h
        · exact h3 i h
        · rw [h]; omega
      · exact h3 i hi
    | Housekept =>
      simp only [inv, step, Sharing.Run.step]
      refine ⟨Int.le_refl _, by omega, fun i hi => ?_⟩
      rw [Sharing.Lemmas.housekept_eq _ hR'] at hi
      split at hi
      · simp only [Sharing.Notifications.warnCode, Sharing.Audit.forgetCode, Sharing.AccessRequests.chaseCode, Sharing.Housekeeping.tidyCode, List.mem_filter, decide_eq_true_eq] at hi
        exact (openIs i m.now).1 hi.2
      · next hn =>
        have hi' : i ∈ (Sharing.Notifications.warnCode (Sharing.AccessRequests.chaseCode isPending reminderDue (Sharing.Audit.forgetCode (Sharing.Housekeeping.tidyCode gone inForce isOpen m.library m.now) m.now) m.now) m.now).invitations := by
          rw [Classical.not_not.mp hn]; exact hi
        simp only [Sharing.Notifications.warnCode, Sharing.Audit.forgetCode, Sharing.AccessRequests.chaseCode, Sharing.Housekeeping.tidyCode, List.mem_filter, decide_eq_true_eq] at hi'
        exact (openIs i m.now).1 hi'.2
    | Delivered =>
      simp only [inv, step, Sharing.Run.step]
      split <;> exact ⟨h1, h2, h3⟩
    | Waited d =>
      simp only [ok] at he
      simp only [inv, step, Sharing.Run.step]
      exact ⟨by omega, by omega, fun i hi => h3 i hi⟩
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
  intro i hi
  simp only [Sharing.Run.after] at hi ⊢
  have := h3 i hi
  omega

end Sharing.InvitationsLapseOnTime.Proofs
