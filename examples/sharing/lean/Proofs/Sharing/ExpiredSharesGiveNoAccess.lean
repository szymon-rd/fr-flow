import FrFlowGen.Sharing.ExpiredSharesGiveNoAccess.Spec

/-! Authored proofs of the obligations of ExpiredSharesGiveNoAccess. Each states exactly its `Obl`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical


namespace Sharing.ExpiredSharesGiveNoAccess.Proofs
open Sharing.ExpiredSharesGiveNoAccess

/-- Access keeps only shares in force; a share in force has not ended (InForceContract): dropping the ended shares first
changes nothing. -/
theorem complete : Obl.complete := by
  unfold Obl.complete
  intro inForce hF
  unfold Sharing.ExpiredSharesGiveNoAccess.claim
  intro lib t p d
  simp only [Sharing.Sharing.accessCode, Sharing.Sharing.granteesOf, Sharing.Sharing.placesOf, Sharing.inTrash, List.filter_filter]
  congr 2
  apply List.filter_congr
  intro s _
  have h := hF s t
  simp only [Sharing.InForceContract.post] at h
  rw [h]
  cases s.«until» <;> simp (config := { contextual := true })

end Sharing.ExpiredSharesGiveNoAccess.Proofs
