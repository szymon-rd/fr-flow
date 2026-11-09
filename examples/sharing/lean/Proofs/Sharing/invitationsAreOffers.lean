import FrFlowGen.Sharing.invitationsAreOffers.Spec
import Proofs.Sharing.Lemmas

/-! The branch is its parts, line by line: who offers (onlyEditorsInvite); that inviting gives no access and who takes
an offer up, of the code, as invitingGivesNoAccess and onlyTheInvitedAccept say for every word it calls (access reads
no invitation: inTrash); and, at every moment, each invitation held is
open as of one housekeeping period ago: invitationsLapseOnTime, read through what open is (isOpenContract). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.invitationsAreOffers.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro inForce reaches covers ownedBy inTrash mayEdit hTrash hInvite _ _ _ hLapse world g0 g1 g2 g3 g4 g5 g6
  -- Inviting and accepting, of their code (the parts state them for every word the code calls).
  have key : ∀ (lib : Library) X t p d, accessCode inTrash inForce { lib with invitations := X } t p d =
      accessCode inTrash inForce lib t p d := by
    intro lib X t p d
    have ht := hTrash
    unfold Sharing.inTrash.claim at ht
    simp only [accessCode, ht]
    rfl
  refine ⟨fun lib t by_ to what level => ⟨⟨hInvite lib t by_ to what level, fun p d => ?_⟩, fun h => ?_⟩,
    fun i hi => ?_⟩
  · simp only [inviteCode]
    split
    · exact key _ _ _ _ _
    · rfl
  · simp only [changes, acceptCode] at h
    split at h
    · exact absurd rfl h
    · next i heq =>
      exact ⟨i, List.mem_of_find?_eq_some heq, by simpa using List.find?_some heq⟩
  · have := hLapse world g0 g1 g2 g3 g4 g5 g6 i hi
    simp only [isOpenCode]
    omega

end Sharing.invitationsAreOffers.Proofs
