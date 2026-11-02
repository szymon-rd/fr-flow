import FrFlowGen.Sharing.requestsAnsweredOnTime.Spec
import Proofs.Sharing.Lemmas

/-! By induction over the run (`FrFlow.always_when`): housekeeping last ran at most two minutes ago, and every
access request held was made less than 7 days before that run, and is reminded or was made less than 48 hours
before it. A request asks only now, unreminded, or keeps requests the library held (recording and announcing it touch
only the log and the outbox); housekeeping keeps only pending requests and reminds those due; delivery touches only
the outbox; a wait keeps within two minutes of the last run (housekeepingOnTime) and never goes back
(clockNeverGoesBack). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.requestsAnsweredOnTime.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro events startedAt reaches covers _ _ _ _ _ _ _ _ _ _ _ _ hBack hOnTime
  let step := fun m e => Sharing.step (mayEditCode inForceCode reaches covers) ownedByCode (isOpenCode 604800)
    (goneCode 2592000) (isPendingCode 604800) (reminderDueCode 172800) inForceCode m e
  let ok : Moment → Event → Prop := fun m e => match e with
    | Event.Waited d => 0 ≤ d ∧ m.now + d ≤ m.tidied + 120
    | _ => True
  let inv : Moment → Prop := fun m => m.tidied ≤ m.now ∧ m.now ≤ m.tidied + 120 ∧
    ∀ q ∈ m.library.requests, m.tidied < q.asked + 604800 ∧ (q.reminded ∨ m.tidied < q.asked + 172800)
  have kept : ∀ m e, inv m → ok m e → inv (step m e) := by
    intro m e ⟨h1, h2, h3⟩ he
    cases e with
    | Asked r =>
      simp only [inv, step, Sharing.step]
      refine ⟨h1, h2, fun q hq => ?_⟩
      rcases Lemmas.served_cases _ _ _ _ _ m.library m.now r with h | ⟨_, _, h, _⟩
      · rw [h] at hq; exact h3 q hq
      · rw [h] at hq
        rcases Lemmas.answered_requests _ _ _ _ _ m.library m.now r q hq with h' | ⟨h', _⟩
        · exact h3 q h'
        · exact ⟨by omega, Or.inr (by omega)⟩
    | Housekept =>
      simp only [inv, step, Sharing.step]
      refine ⟨Int.le_refl _, by omega, fun q hq => ?_⟩
      rw [(Lemmas.housekept_parts _ _ _ _ _ m.library m.now).2.2] at hq
      simp only [chaseCode, tidyCode, List.mem_map, List.mem_filter] at hq
      obtain ⟨q0, ⟨_, hp⟩, rfl⟩ := hq
      have hp' := of_decide_eq_true hp
      simp only [isPendingCode] at hp'
      simp only [chased, reminderDueCode]
      by_cases hc : q0.asked + 172800 ≤ m.now ∧ ¬ q0.reminded
      · simp only [hc, not_false_eq_true, and_self, ↓reduceIte]
        exact ⟨hp', Or.inl trivial⟩
      · simp only [hc, ↓reduceIte]
        refine ⟨hp', ?_⟩
        by_cases hr : q0.reminded
        · exact Or.inl hr
        · have : ¬ (q0.asked + 172800 ≤ m.now) := fun h => hc ⟨h, hr⟩
          exact Or.inr (by omega)
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
  intro q hq
  obtain ⟨h4, h5⟩ := h3 q hq
  show (List.foldl step _ events).now < q.asked + 604800 + 120 ∧
    (q.reminded ∨ (List.foldl step _ events).now < q.asked + 172800 + 120)
  refine ⟨by omega, ?_⟩
  rcases h5 with h5 | h5
  · exact Or.inl h5
  · exact Or.inr (by omega)

end Sharing.requestsAnsweredOnTime.Proofs
