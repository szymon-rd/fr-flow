import FrFlowGen.Sharing.auditTrail.Spec
import Proofs.Sharing.Lemmas

/-! By induction over the run (`FrFlow.always_when`): every share held has an entry in the log that made it. A request
that changes the library is recorded in the same step, so a share it makes comes with its entry, and the entries
before stay (the operations leave the log alone, announcing touches only the outbox); housekeeping only removes
shares, forgets no entry explaining a share it keeps, and adds an entry; delivery and waiting change neither. A yes
of viewing rests on a share held, which has its entry. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.auditTrail.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro events startedAt _ _ _ _ _ _
  let step := fun m e => Sharing.step (mayEditCode inForceCode reachesCode coversCode) ownedByCode (isOpenCode 604800)
    (goneCode 2592000) (isPendingCode 604800) (reminderDueCode 172800) inForceCode m e
  let inv : Moment → Prop := fun m => ∀ s ∈ m.library.shares, ∃ e ∈ m.library.log, makes e s
  have kept : ∀ m e, inv m → True → inv (step m e) := by
    intro m e h _
    cases e with
    | Asked r =>
      simp only [inv, step, Sharing.step]
      intro s hs
      rcases Lemmas.served_logged _ _ _ _ _ m.library m.now r with hc | ⟨hsh, hlog, _⟩
      · rw [hc] at hs ⊢; exact h s hs
      · rw [hsh] at hs
        rw [hlog, Lemmas.answered_log]
        rcases Lemmas.answered_shares _ _ _ _ _ m.library m.now r (m.library.log.length : Int) s hs with h1 | h1
        · obtain ⟨e, he, hm⟩ := h s h1
          exact ⟨e, List.mem_append_left _ he, hm⟩
        · exact ⟨_, List.mem_append_right _ (List.mem_singleton.2 rfl), h1⟩
    | Housekept =>
      simp only [inv, step, Sharing.step, housekept]
      intro s hs
      split at hs
      · next hc =>
        rw [if_pos hc]
        simp only [recordCode, warnCode, forgetCode, chaseCode, tidyCode, List.mem_filter, List.mem_append,
          List.mem_singleton] at hs ⊢
        obtain ⟨e, he, hm⟩ := h s hs.1
        refine ⟨e, Or.inl (List.mem_map.2 ⟨e, he, ?_⟩), hm⟩
        exact if_neg (fun hx => hx.2 (Or.inl ⟨s, List.mem_filter.2 hs, hm⟩))
      · next hc => rw [if_neg hc]; exact h s hs
    | Delivered p =>
      simp only [inv, step, Sharing.step]
      split
      · exact h
      · exact h
    | Waited d =>
      simp only [inv, step, Sharing.step]
      exact h
  have h := FrFlow.always_when step (fun _ _ => True) inv
    (Moment.mk (Library.mk [] [] [] [] [] [] [] []) startedAt startedAt []) (by simp [inv]) kept events
    (fun _ _ _ _ => trivial)
  refine ⟨h, fun p d hv => ?_⟩
  simp only [mayViewCode] at hv
  obtain ⟨s, hs, hv⟩ := hv
  exact ⟨s, hs, hv, h s hs⟩

end Sharing.auditTrail.Proofs
