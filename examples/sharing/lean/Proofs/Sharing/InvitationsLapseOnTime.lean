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
invitations only now; housekeeping keeps only open ones (IsOpenContract); a wait keeps within two minutes of the last
run (HousekeepingOnTime) and never goes back (ClockNeverGoesBack). -/
theorem complete : Obl.complete := by
  unfold Obl.complete
  intro events startedAt inForce isOpen gone tidy housekeep _ hO hC hH
  unfold Sharing.InvitationsLapseOnTime.claim
  have hL : (0 : Int) < Sharing.invitationLasts := by simp [Sharing.invitationLasts]
  have hW : (0 : Int) ≤ Sharing.housekeepingWithin := by simp [Sharing.housekeepingWithin]
  let ok : Moment → Event → Prop := fun m e => match e with
    | Event.Waited d => 0 ≤ d ∧ m.now + d ≤ m.tidied + Sharing.housekeepingWithin
    | _ => True
  let inv : Moment → Prop := fun m => m.tidied ≤ m.now ∧ m.now ≤ m.tidied + Sharing.housekeepingWithin ∧
    ∀ i ∈ m.library.invitations, m.tidied < i.sent + Sharing.invitationLasts
  have kept : ∀ m e, inv m → ok m e →
      inv (Sharing.Run.step (Sharing.mayEdit inForce Sharing.reaches Sharing.covers) isOpen gone inForce m e) := by
    intro m e ⟨h1, h2, h3⟩ he
    cases e with
    | Asked r =>
      simp only [inv, Sharing.Run.step]
      refine ⟨h1, h2, fun i hi => ?_⟩
      rcases Sharing.Lemmas.answered_invitations _ _ _ _ _ r i hi with h | h
      · exact h3 i h
      · rw [h]; omega
    | Housekept =>
      simp only [inv, Sharing.Run.step, Sharing.Housekeeping.tidyCode, List.mem_filter, decide_eq_true_eq]
      refine ⟨Int.le_refl _, by omega, fun i hi => ?_⟩
      have := hO i m.now
      simp only [Sharing.IsOpenContract.post] at this
      rw [this] at hi
      exact hi.2
    | Waited d =>
      simp only [ok] at he
      simp only [inv, Sharing.Run.step]
      exact ⟨by omega, by omega, fun i hi => h3 i hi⟩
  have h := FrFlow.always_when (fun m e => Sharing.Run.step (Sharing.mayEdit inForce Sharing.reaches Sharing.covers) isOpen gone inForce m e)
    ok inv (Moment.mk (Library.mk [] [] [] [] []) startedAt startedAt) ⟨Int.le_refl _, by simp only; omega, by simp⟩ kept events
    (fun pre e post hp => by
      have hc := hC pre post e hp
      have hh := hH pre post e hp
      cases e with
      | Waited d => exact ⟨hc, hh⟩
      | _ => trivial)
  obtain ⟨_, h2, h3⟩ := h
  intro i hi
  simp only [Sharing.Run.after] at hi ⊢
  have := h3 i hi
  omega

end Sharing.InvitationsLapseOnTime.Proofs
