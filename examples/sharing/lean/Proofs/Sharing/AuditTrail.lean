import FrFlowGen.Sharing.AuditTrail.Spec
import Proofs.Sharing.Lemmas

/-! Authored proofs of the obligations of AuditTrail. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Sharing.AuditTrail.Proofs
open Sharing.AuditTrail

/-- By induction over the run (`FrFlow.always_when`): every share held has an entry in the log that made it. A request
that changes the library is recorded in the same step (RecordContract), so a share it makes comes with its entry, and
the entries before stay (the operations leave the log alone, announcing touches only the outbox); housekeeping only
removes shares and adds an entry; delivery and waiting change neither. A yes of viewing rests on a share held, which
has its entry. -/
theorem complete : Obl.complete := by
  unfold Obl.complete
  intro events inForce startedAt announce record isOpen gone isPending reminderDue hR hA
  have hR' : ∀ l t c, record l t c = { l with log := l.log ++ [Entry.mk (l.log.length : Int) t c] } := fun l t c => hR l t c
  have hA' : ∀ l b r e, announce l b r e = { l with outbox := l.outbox ++ Notifications.noticesOf b r e } := fun l b r e => hA l b r e
  unfold Sharing.AuditTrail.claim
  let inv : Moment → Prop := fun m => ∀ s ∈ m.library.shares, ∃ e ∈ m.library.log, Sharing.Audit.makes e s
  let step := fun m e => Sharing.Run.step announce record (Sharing.mayEdit inForce Sharing.reaches Sharing.covers) Sharing.ownedBy isOpen
    gone isPending reminderDue inForce m e
  have kept : ∀ m e, inv m → True → inv (step m e) := by
    intro m e h _
    cases e with
    | Asked r =>
      simp only [inv, step, Sharing.Run.step]
      intro s hs
      rw [Sharing.Lemmas.served_eq _ _ hR' hA'] at hs ⊢
      split at hs
      · next hc =>
        rw [if_pos hc]
        simp only [Sharing.Lemmas.answered_log, List.mem_append, List.mem_singleton]
        rcases Sharing.Lemmas.answered_shares _ _ _ _ _ m.library m.now r
          ((Sharing.Run.answered (Sharing.mayEdit inForce Sharing.reaches Sharing.covers) Sharing.ownedBy isOpen gone isPending
            m.library m.now r).log.length : Int) s hs with h1 | h1
        · obtain ⟨e, he, hm⟩ := h s h1
          exact ⟨e, Or.inl he, hm⟩
        · exact ⟨_, Or.inr rfl, by rw [Sharing.Lemmas.answered_log] at h1; exact h1⟩
      · next hc => rw [if_neg hc]; exact h s hs
    | Housekept =>
      simp only [inv, step, Sharing.Run.step]
      intro s hs
      rw [Sharing.Lemmas.housekept_eq _ hR'] at hs ⊢
      split at hs
      · next hc =>
        rw [if_pos hc]
        simp only [Sharing.AccessRequests.chaseCode, Sharing.Housekeeping.tidyCode, List.mem_filter, List.mem_append,
          List.mem_singleton] at hs ⊢
        obtain ⟨e, he, hm⟩ := h s hs.1
        exact ⟨e, Or.inl he, hm⟩
      · next hc => rw [if_neg hc]; exact h s hs
    | Delivered =>
      simp only [inv, step, Sharing.Run.step]
      split
      · exact h
      · exact h
    | Waited d =>
      simp only [inv, step, Sharing.Run.step]
      exact h
  have h := FrFlow.always_when step (fun _ _ => True) inv
    (Moment.mk (Library.mk [] [] [] [] [] [] [] []) startedAt startedAt []) (by simp [inv]) kept events (fun _ _ _ _ => trivial)
  simp only [step, inv] at h
  simp only [Sharing.Run.after]
  refine ⟨h, fun p d hv => ?_⟩
  simp only [Sharing.mayView] at hv
  obtain ⟨s, hs, hv⟩ := hv
  exact ⟨s, hs, hv, h s hs⟩

end Sharing.AuditTrail.Proofs
