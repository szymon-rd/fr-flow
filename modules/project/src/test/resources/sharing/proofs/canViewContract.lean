import FrFlowGen.Sharing.canViewContract.Spec

/-! A person can view a document exactly when their access is some level: `canViewCode` is that, read off the
access worked out. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.canViewContract.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intros
  intro _ _ _ _
  rfl

end Sharing.canViewContract.Proofs
