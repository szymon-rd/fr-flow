import FrFlowGen.Sharing.auditTrail.Spec
import Proofs.Sharing.Lemmas

/-! Every share held has an entry in the log that made it: what the World's `logKept` keeps at every moment (each step
keeping it is logKept's own cover). A yes of viewing, what permission says it is, rests on a share held, which has its
entry. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.auditTrail.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro mayView record forget announce hPerm _ _ _ world _ _ hLog
  have h := hLog.1
  refine ⟨h, fun p d hv => ?_⟩
  unfold Sharing.permission.claim at hPerm
  rw [hPerm] at hv
  obtain ⟨s, hs, hv⟩ := hv
  exact ⟨s, hs, hv, h s hs⟩

end Sharing.auditTrail.Proofs
