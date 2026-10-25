import FrFlowGen.Sharing.NoticesFollowChanges.Spec
import Proofs.Sharing.Lemmas

/-! Authored proofs of the obligations of NoticesFollowChanges. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Sharing.NoticesFollowChanges.Proofs
open Sharing.NoticesFollowChanges

/-- A notice of a logged change waiting in the outbox is of an entry in the log; it stays so as the log grows. -/
theorem kept_more (log more : List Entry) (n : Notice) (h : ∀ e, n.about = Subject.Logged e → e ∈ log) :
    ∀ e, n.about = Subject.Logged e → e ∈ log ++ more :=
  fun e he => List.mem_append_left _ (h e he)

/-- By induction over the run (`FrFlow.always_when`). A request that changes the library is recorded and announced in the
one step (RecordContract, AnnounceContract): its notices are of its entry, now in the log; the log only grows.
Housekeeping's notices are of no logged change, and it forgets no entry a waiting notice is of (ForgetContract's
code). Delivery takes a person's oldest notice out of the outbox to the mail server, which keeps it once. -/
theorem complete : Obl.complete := by
  unfold Obl.complete
  intro events startedAt announce record inForce isOpen gone isPending reminderDue warn deliver hR hA _ _
  have hR' : ∀ l t c, record l t c = { l with log := l.log ++ [Entry.mk (l.log.length : Int) t c] } := fun l t c => hR l t c
  have hA' : ∀ l b r e, announce l b r e = { l with outbox := l.outbox ++ Notifications.noticesOf b r e } := fun l b r e => hA l b r e
  unfold Sharing.NoticesFollowChanges.claim
  let inv : Moment → Prop := fun m => (∀ n ∈ m.library.outbox, ∀ e, n.about = Subject.Logged e → e ∈ m.library.log) ∧
    ∀ n ∈ m.mailbox, ((List.filter (fun x => decide (x = n)) m.mailbox).length : Int) = 1
  let step := fun m e => Sharing.Run.step announce record (Sharing.mayEdit inForce Sharing.reaches Sharing.covers) Sharing.ownedBy isOpen
    gone isPending reminderDue inForce m e
  have keptStep : ∀ m e, inv m → True → inv (step m e) := by
    intro m e ⟨h1, h2⟩ _
    cases e with
    | Asked r =>
      simp only [inv, step, Sharing.Run.step]
      rw [Sharing.Lemmas.served_eq _ _ hR' hA']
      split
      · refine ⟨fun n hn => ?_, h2⟩
        simp only [Sharing.Lemmas.answered_outbox, Sharing.Lemmas.answered_log, List.mem_append] at hn ⊢
        rcases hn with hn | hn
        · exact fun e he => Or.inl (h1 n hn e he)
        · intro e he
          rw [Sharing.Lemmas.noticesOf_logged _ _ _ n hn] at he
          cases he
          simp
      · exact ⟨h1, h2⟩
    | Housekept =>
      simp only [inv, step, Sharing.Run.step]
      rw [Sharing.Lemmas.housekept_eq _ hR']
      split
      · refine ⟨fun n hn => ?_, h2⟩
        simp only [Sharing.Notifications.warnCode, Sharing.Audit.forgetCode, Sharing.AccessRequests.chaseCode, Sharing.Housekeeping.tidyCode, List.mem_append] at hn ⊢
        rcases hn with (hn | hn) | hn
        · -- a waiting notice's entry explains something: it is not forgotten
          exact fun e he => Or.inl (List.mem_map.2 ⟨e, h1 n hn e he, if_neg (fun hx => hx.2 (Or.inr ⟨n, hn, he⟩))⟩)
        · intro e he
          exact absurd he (Sharing.Lemmas.chaseNotices_unlogged _ _ _ _ n hn e)
        · intro e he
          simp only [Sharing.Notifications.endingNotices, List.mem_flatMap, List.mem_map] at hn
          obtain ⟨_, _, _, _, rfl⟩ := hn
          cases he
      · exact ⟨h1, h2⟩
    | Delivered =>
      simp only [inv, step, Sharing.Run.step]
      split
      · next n hn =>
        have hn' : n ∈ m.library.outbox := List.mem_of_find?_eq_some hn
        refine ⟨fun x hx => ?_, fun x hx => ?_⟩
        · simp only [List.mem_filter] at hx
          exact h1 x hx.1
        · by_cases hin : n ∈ m.mailbox
          · simp only [hin, ite_true] at hx ⊢; exact h2 x hx
          · have hnot := hin
            simp only [hin, ite_false] at hx ⊢
            simp only [List.filter_append, List.length_append, List.mem_append, List.mem_singleton] at hx ⊢
            rcases hx with hx | rfl
            · have := h2 x hx
              have hne : x ≠ n := fun h => hnot (h ▸ hx)
              have h0 : List.filter (fun y => decide (y = x)) [n] = [] := by simp [Ne.symm hne]
              rw [h0]; simpa using this
            · have : List.filter (fun y => decide (y = x)) m.mailbox = [] := by
                rw [List.filter_eq_nil_iff]; intro y hy; simp only [decide_eq_true_eq]; exact fun h => hnot (h ▸ hy)
              simp [this]
      · exact ⟨h1, h2⟩
    | Waited d =>
      simp only [inv, step, Sharing.Run.step]
      exact ⟨h1, h2⟩
  have h := FrFlow.always_when step (fun _ _ => True) inv
    (Moment.mk (Library.mk [] [] [] [] [] [] [] []) startedAt startedAt []) (by simp [inv]) keptStep events (fun _ _ _ _ => trivial)
  simp only [step, inv] at h
  simp only [Sharing.Run.after]
  refine ⟨fun n hn => ?_, h.2⟩
  have hk := h.1 n hn
  split
  · next e he => exact hk e he
  · trivial
  · trivial
  · trivial

end Sharing.NoticesFollowChanges.Proofs
