import FrFlowGen.Sharing.trashPurgedOnTime.Spec
import Proofs.Sharing.Lemmas

/-! By induction over the run (`FrFlow.always_when`): housekeeping last ran at most two minutes ago, and every
document in the trash went there less than 30 days before that run. A request puts documents in the trash only now,
or keeps a time the library held (recording and announcing it touch only the log and the outbox); housekeeping keeps
only documents not gone; delivery touches only the outbox; a wait keeps within two minutes of the last run
(housekeepingOnTime) and never goes back (clockNeverGoesBack). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.trashPurgedOnTime.Proofs
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
    ∀ doc ∈ m.library.documents, ∀ a, doc.trashed = some a → m.tidied < a + 2592000
  have kept : ∀ m e, inv m → ok m e → inv (step m e) := by
    intro m e ⟨h1, h2, h3⟩ he
    cases e with
    | Asked r =>
      simp only [inv, step, Sharing.step]
      refine ⟨h1, h2, fun doc hd a ha => ?_⟩
      rcases Lemmas.served_cases _ _ _ _ _ m.library m.now r with h | ⟨h, _⟩
      · rw [h] at hd; exact h3 doc hd a ha
      · rw [h] at hd
        rcases Lemmas.answered_documents _ _ _ _ _ m.library m.now r doc hd with h' | h' | ⟨x, hx, h'⟩
        · rw [h'] at ha; cases ha
        · rw [h'] at ha; cases ha; omega
        · exact h3 x hx a (h'.trans ha)
    | Housekept =>
      simp only [inv, step, Sharing.step]
      refine ⟨Int.le_refl _, by omega, fun doc hd a ha => ?_⟩
      rw [(Lemmas.housekept_parts _ _ _ _ _ m.library m.now).1] at hd
      simp only [tidyCode, List.mem_filter, decide_eq_true_eq, goneCode, ha, Option.some.injEq, exists_eq_left']
        at hd
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
  intro doc hd a ha
  have := h3 doc hd a ha
  show (List.foldl step _ events).now < a + 2592000 + 120
  omega

end Sharing.trashPurgedOnTime.Proofs
