import FrFlowGen.Sharing.invitingGivesNoAccess.Spec
import Proofs.Sharing.Lemmas

/-! An invitation changes only the invitations, which access does not read (whether a document is in the trash
reads its documents, inTrash). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.invitingGivesNoAccess.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro mayEdit inTrash inForce hTrash _ _ lib t by_ to what level p d
  have key : ∀ X, accessCode inTrash inForce { lib with invitations := X } t p d =
      accessCode inTrash inForce lib t p d := by
    intro X
    have ht := hTrash
    unfold Sharing.inTrash.claim at ht
    simp only [accessCode, ht]
    rfl
  simp only [inviteCode]
  split
  · exact key _
  · rfl

end Sharing.invitingGivesNoAccess.Proofs
