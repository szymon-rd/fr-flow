import FrFlowGen.Sharing.canEditContract.Spec

/-! A person can edit a document exactly when their access is edit: `canEditCode` is that, read off the access
worked out. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.canEditContract.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intros
  intro _ _ _ _
  rfl

end Sharing.canEditContract.Proofs
