import FrFlowGen.Sharing.invitationsAreOffers.Spec
import Proofs.Sharing.Lemmas

/-! Inviting and withdrawing change the library only when the asker may edit; an invitation changes only the
invitations, which access does not read (whether a document is in the trash reads its documents, `inTrash`);
accepting changes it only through an open invitation of the person to what they accept. At every moment each
invitation held is open as of one housekeeping period ago: invitationsLapseOnTime. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.invitationsAreOffers.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro reaches covers inTrash events startedAt inForce hTrash _ _ _ _ _ hLapse
  refine ⟨⟨fun lib t by_ to what => ⟨fun h => Lemmas.changed h, fun level => ⟨fun h => Lemmas.changed h,
    fun p d => ?_⟩⟩, fun lib t p what h => ?_⟩, fun i hi => ?_⟩
  · have key : ∀ X, accessCode inTrash inForceCode { lib with invitations := X } t p d =
        accessCode inTrash inForceCode lib t p d := by
      intro X
      have ht := hTrash
      unfold Sharing.inTrash.claim at ht
      simp only [accessCode, ht]
      rfl
    simp only [inviteCode]
    split
    · exact key _
    · rfl
  · simp only [acceptCode] at h
    split at h
    · exact absurd rfl h
    · next i heq =>
      exact ⟨i, List.mem_of_find?_eq_some heq, by simpa using List.find?_some heq⟩
  · have := hLapse i hi
    simp only [isOpenCode]
    omega

end Sharing.invitationsAreOffers.Proofs
