import FrFlowGen.Sharing.viewingRestsOnTheLog.Spec
import Proofs.Sharing.Lemmas

/-! A yes of viewing, what permission says it is, rests on a share held, which has its entry: what the World's
sharesLogged keeps at every moment. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.viewingRestsOnTheLog.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro mayView hPerm p d world _ _ _ _ _ g5 _ hv
  unfold Sharing.permission.claim at hPerm
  rw [hPerm] at hv
  obtain ⟨s, hs, hv⟩ := hv
  exact ⟨s, hs, hv, g5 s hs⟩

end Sharing.viewingRestsOnTheLog.Proofs
