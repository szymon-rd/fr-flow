import FrFlowGen.Sharing.invitationsLapseOnTime.Spec
import Proofs.Sharing.Lemmas

/-! By induction over the run (`FrFlow.always_when`): housekeeping last ran at most two minutes ago, and every
invitation held was sent less than 7 days before that run. A request sends invitations only now, or keeps ones the
library held (recording and announcing it touch only the log and the outbox); housekeeping keeps only open
invitations; delivery touches only the outbox; a wait keeps within two minutes of the last run (housekeepingOnTime)
and never goes back (clockNeverGoesBack). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.invitationsLapseOnTime.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro events startedAt reaches covers _ _ _ _ _ _ _ _ _ _ _ hBack hOnTime
  let step := fun m e => Sharing.step (mayEditCode inForceCode reaches covers) ownedByCode (isOpenCode 604800)
    (goneCode 2592000) (isPendingCode 604800) (reminderDueCode 172800) inForceCode m e
  let ok : Moment → Event → Prop := fun m e => match e with
    | Event.Waited d => 0 ≤ d ∧ m.now + d ≤ m.tidied + 120
    | _ => True
  let inv : Moment → Prop := fun m => m.tidied ≤ m.now ∧ m.now ≤ m.tidied + 120 ∧
    ∀ i ∈ m.library.invitations, m.tidied < i.sent + 604800
  have kept : ∀ m e, inv m → ok m e → inv (step m e) := by
    intro m e ⟨h1, h2, h3⟩ he
    cases e with
    | Asked r =>
      simp only [inv, step, Sharing.step]
      refine ⟨h1, h2, fun i hi => ?_⟩
      rcases Lemmas.served_cases _ _ _ _ _ m.library m.now r with h | ⟨_, h, _⟩
      · rw [h] at hi; exact h3 i hi
      · rw [h] at hi
        rcases Lemmas.answered_invitations _ _ _ _ _ m.library m.now r i hi with h' | h'
        · exact h3 i h'
        · omega
    | Housekept =>
      simp only [inv, step, Sharing.step]
      refine ⟨Int.le_refl _, by omega, fun i hi => ?_⟩
      rw [(Lemmas.housekept_parts _ _ _ _ _ m.library m.now).2.1] at hi
      simp only [tidyCode, List.mem_filter] at hi
      have := of_decide_eq_true hi.2
      simp only [isOpenCode] at this
      omega
    | Delivered p =>
      simp only [inv, step, Sharing.step]
      split
      · exact ⟨h1, h2, h3⟩
      · exact ⟨h1, h2, h3⟩
    | Waited d =>
      simp only [ok] at he
      simp only [inv, step, Sharing.step]
      exact ⟨by omega, by omega, h3⟩
  have h := FrFlow.always_when step ok inv
    (Moment.mk (Library.mk [] [] [] [] [] [] [] []) startedAt startedAt []) ⟨Int.le_refl _, show startedAt ≤ startedAt + 120 by omega, by simp⟩ kept
    events (fun pre e post hp => by
      have hc := hBack pre e post hp
      have hh := hOnTime pre e post hp
      cases e with
      | Waited d => exact ⟨hc, hh⟩
      | _ => trivial)
  obtain ⟨_, h2, h3⟩ := h
  intro i hi
  have := h3 i hi
  show (List.foldl step _ events).now < i.sent + 604800 + 120
  omega

end Sharing.invitationsLapseOnTime.Proofs
