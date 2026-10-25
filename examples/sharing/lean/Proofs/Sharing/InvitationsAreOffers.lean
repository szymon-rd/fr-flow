import FrFlowGen.Sharing.InvitationsAreOffers.Spec
import Proofs.Sharing.Lemmas

/-! Authored proofs of the obligations of InvitationsAreOffers. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Sharing.InvitationsAreOffers.Proofs
open Sharing.InvitationsAreOffers

/-- The operations by their contracts; that a lapsed invitation is gone within one period of housekeeping is
InvitationsLapseOnTime's deadline, read through IsOpenContract. -/
theorem complete : Obl.complete := by
  unfold Obl.complete
  frflow_intro
  unfold Sharing.InvitationsAreOffers.claim
  refine ⟨?_, ?_⟩
  · clear h_InvitationsLapseOnTime h_IsOpenContract
    simp only [frflow_defs] at *
    refine ⟨fun lib t by_ to what => ⟨fun h => ?_, fun level => ⟨fun h => ?_, fun p d => ?_⟩⟩, fun lib t p what h => ?_⟩
    · rw [h_WithdrawContract] at h; exact Sharing.Lemmas.changed h
    · rw [h_InviteContract] at h; exact Sharing.Lemmas.changed h
    · -- An invitation changes only the invitations, which access does not read.
      have key : ∀ X, access { lib with invitations := X } t p d = access lib t p d := by
        intro X; rw [h_AccessContract, h_AccessContract]; rfl
      rw [h_InviteContract]
      exact Sharing.Lemmas.ite_same (fun L => access L t p d) _ _ (key _)
    · rw [h_AcceptContract] at h
      split at h
      · next i heq => exact ⟨i, List.mem_of_find?_eq_some heq, by simpa using List.find?_some heq⟩
      · exact absurd rfl h
  · have hO : ∀ i t, isOpen i t ↔ t < i.sent + Sharing.invitationLasts := by
      intro i t
      have := h_IsOpenContract i t
      simp only [Sharing.IsOpenContract.post] at this
      rw [this]
    have h := h_InvitationsLapseOnTime
    unfold Sharing.InvitationsLapseOnTime.claim at h
    intro i hi
    rw [hO]
    have := h i hi
    omega

end Sharing.InvitationsAreOffers.Proofs
