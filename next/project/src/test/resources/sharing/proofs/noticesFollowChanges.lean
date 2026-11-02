import FrFlowGen.Sharing.noticesFollowChanges.Spec
import Proofs.Sharing.Lemmas

/-! By induction over the run (`FrFlow.always_when`). A request that changes the library is recorded and announced in
the one step: its notices are of its entry, now in the log; the log only grows. Housekeeping's notices are of no
logged change, and it forgets no entry a waiting notice is of. Delivery takes a person's oldest notice out of the
outbox to the mail server, which keeps it once. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.noticesFollowChanges.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro events startedAt reaches covers _ _ _ _ _ _ _ _
  let step := fun m e => Sharing.step (mayEditCode inForceCode reaches covers) ownedByCode (isOpenCode 604800)
    (goneCode 2592000) (isPendingCode 604800) (reminderDueCode 172800) inForceCode m e
  let inv : Moment → Prop := fun m => (∀ n ∈ m.library.outbox, ∀ e, n.about = Subject.Logged e → e ∈ m.library.log) ∧
    ∀ n ∈ m.mailbox, ((List.filter (fun x => decide (x = n)) m.mailbox).length : Int) = 1
  have kept : ∀ m e, inv m → True → inv (step m e) := by
    intro m e ⟨h1, h2⟩ _
    cases e with
    | Asked r =>
      simp only [inv, step, Sharing.step]
      rcases Lemmas.served_logged _ _ _ _ _ m.library m.now r with hc | ⟨_, hlog, hout⟩
      · rw [hc]; exact ⟨h1, h2⟩
      · refine ⟨fun n hn => ?_, h2⟩
        rw [hout, Lemmas.answered_outbox, List.mem_append] at hn
        rw [hlog, Lemmas.answered_log]
        rcases hn with hn | hn
        · exact fun e he => List.mem_append_left _ (h1 n hn e he)
        · intro e he
          rw [Lemmas.noticesOf_logged _ _ _ n hn] at he
          cases he
          exact List.mem_append_right _ (List.mem_singleton.2 (by rw [Lemmas.answered_log]))
    | Housekept =>
      simp only [inv, step, Sharing.step, housekept]
      split
      · refine ⟨fun n hn => ?_, h2⟩
        simp only [recordCode, warnCode, forgetCode, chaseCode, tidyCode, List.mem_append] at hn ⊢
        rcases hn with (hn | hn) | hn
        · exact fun e he => Or.inl (List.mem_map.2 ⟨e, h1 n hn e he, if_neg (fun hx => hx.2 (Or.inr ⟨n, hn, he⟩))⟩)
        · intro e he
          exact absurd he (Lemmas.chaseNotices_unlogged _ _ _ _ n hn e)
        · intro e he
          exact absurd he (Lemmas.endingNotices_unlogged _ _ n hn e)
      · exact ⟨h1, h2⟩
    | Delivered p =>
      simp only [inv, step, Sharing.step]
      split
      · exact ⟨h1, h2⟩
      · next n hn =>
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
                rw [List.filter_eq_nil_iff]; intro y hy; simp only [decide_eq_true_eq]
                exact fun h => hnot (h ▸ hy)
              simp [this]
    | Waited d =>
      simp only [inv, step, Sharing.step]
      exact ⟨h1, h2⟩
  have h := FrFlow.always_when step (fun _ _ => True) inv
    (Moment.mk (Library.mk [] [] [] [] [] [] [] []) startedAt startedAt []) (by simp [inv]) kept events
    (fun _ _ _ _ => trivial)
  refine ⟨fun n hn => ?_, h.2⟩
  have hk := h.1 n hn
  split
  · next e he => exact hk e he
  · trivial
  · trivial
  · trivial

end Sharing.noticesFollowChanges.Proofs
