import FrFlowGen.Sharing.RequestsAnsweredOnTime.Spec
import Proofs.Sharing.Lemmas

/-! Authored proofs of the obligations of RequestsAnsweredOnTime. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Sharing.RequestsAnsweredOnTime.Proofs
open Sharing.RequestsAnsweredOnTime

/-- By induction over the run (`FrFlow.always_when`), with the last run of housekeeping in the state: housekeeping last
ran at most two minutes ago, every request pending was made less than 7 days before it, and every one not reminded less
than 48 hours before it. A request makes requests only now, not reminded (recording and announcing touch only the log
and the outbox); housekeeping keeps only pending ones (PendingContract) and reminds those due (ReminderDueContract), and
when it changes nothing every one is so already; delivery touches only the outbox; a wait keeps within two minutes of
the last run (HousekeepingOnTime) and never goes back (ClockNeverGoesBack). -/
theorem complete : Obl.complete := by
  unfold Obl.complete
  intro events startedAt announce record inForce isOpen gone isPending reminderDue chase tidy housekeep hR hA _ hP hD hC hH
  have hR' : ∀ l t c, record l t c = { l with log := l.log ++ [Entry.mk (l.log.length : Int) t c] } := fun l t c => hR l t c
  have hA' : ∀ l b r e, announce l b r e = { l with outbox := l.outbox ++ Notifications.noticesOf b r e } := fun l b r e => hA l b r e
  unfold Sharing.RequestsAnsweredOnTime.claim
  have hL : (0 : Int) < Sharing.requestLasts := by simp [Sharing.requestLasts]
  have hM : (0 : Int) < Sharing.remindAfter := by simp [Sharing.remindAfter]
  have hW : (0 : Int) ≤ Sharing.housekeepingWithin := by simp [Sharing.housekeepingWithin]
  have pendingIs : ∀ q t, isPending q t ↔ t < q.asked + Sharing.requestLasts := by
    intro q t; have := hP q t; simp only [Sharing.PendingContract.post] at this; rw [this]
  have dueIs : ∀ q t, reminderDue q t ↔ q.asked + Sharing.remindAfter ≤ t := by
    intro q t; have := hD q t; simp only [Sharing.ReminderDueContract.post] at this; rw [this]
  let ok : Moment → Event → Prop := fun m e => match e with
    | Event.Waited d => 0 ≤ d ∧ m.now + d ≤ m.tidied + Sharing.housekeepingWithin
    | _ => True
  let fine : Int → AccessRequest → Prop := fun at_ q =>
    at_ < q.asked + Sharing.requestLasts ∧ (q.reminded ∨ at_ < q.asked + Sharing.remindAfter)
  let inv : Moment → Prop := fun m => m.tidied ≤ m.now ∧ m.now ≤ m.tidied + Sharing.housekeepingWithin ∧
    ∀ q ∈ m.library.requests, fine m.tidied q
  let step := fun m e => Sharing.Run.step announce record (Sharing.mayEdit inForce Sharing.reaches Sharing.covers) Sharing.ownedBy isOpen
    gone isPending reminderDue inForce m e
  -- What housekeeping leaves of the requests at a moment is fine at that moment.
  have chasedFine : ∀ (lib : Library) (t : Int) q,
      q ∈ (Sharing.AccessRequests.chaseCode isPending reminderDue (Sharing.Housekeeping.tidyCode gone inForce isOpen lib t) t).requests →
      fine t q := by
    intro lib t q hq
    simp only [Sharing.AccessRequests.chaseCode, Sharing.Housekeeping.tidyCode, List.mem_map, List.mem_filter,
      decide_eq_true_eq] at hq
    obtain ⟨r, ⟨_, hp⟩, rfl⟩ := hq
    rw [pendingIs] at hp
    simp only [fine, Sharing.AccessRequests.chased]
    by_cases hc : reminderDue r t ∧ ¬r.reminded
    · simp only [hc]; exact ⟨hp, Or.inl trivial⟩
    · simp only [hc, ite_false]
      refine ⟨hp, ?_⟩
      by_cases hr : r.reminded
      · exact Or.inl hr
      · right; have : ¬ reminderDue r t := fun h => hc ⟨h, hr⟩
        rw [dueIs] at this; omega
  have kept : ∀ m e, inv m → ok m e → inv (step m e) := by
    intro m e ⟨h1, h2, h3⟩ he
    cases e with
    | Asked r =>
      simp only [inv, step, Sharing.Run.step]
      refine ⟨h1, h2, fun q hq => ?_⟩
      rw [Sharing.Lemmas.served_eq _ _ hR' hA'] at hq
      split at hq
      · rcases Sharing.Lemmas.answered_requests _ _ _ _ _ m.library m.now r q hq with h | ⟨ha, _⟩
        · exact h3 q h
        · simp only [fine]; rw [ha]; constructor <;> omega
      · exact h3 q hq
    | Housekept =>
      simp only [inv, step, Sharing.Run.step]
      refine ⟨Int.le_refl _, by omega, fun q hq => ?_⟩
      rw [Sharing.Lemmas.housekept_eq _ hR'] at hq
      split at hq
      · exact chasedFine m.library m.now q hq
      · next hn =>
        apply chasedFine m.library m.now q
        rw [Classical.not_not.mp hn]; exact hq
    | Delivered =>
      simp only [inv, step, Sharing.Run.step]
      split <;> exact ⟨h1, h2, h3⟩
    | Waited d =>
      simp only [ok] at he
      simp only [inv, step, Sharing.Run.step]
      exact ⟨by omega, by omega, fun q hq => h3 q hq⟩
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
  intro q hq
  simp only [Sharing.Run.after] at hq ⊢
  obtain ⟨f1, f2⟩ := h3 q hq
  refine ⟨by omega, ?_⟩
  rcases f2 with f2 | f2
  · exact Or.inl f2
  · right; omega

end Sharing.RequestsAnsweredOnTime.Proofs
