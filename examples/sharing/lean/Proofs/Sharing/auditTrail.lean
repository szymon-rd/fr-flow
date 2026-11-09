import FrFlowGen.Sharing.auditTrail.Spec
import Proofs.Sharing.Lemmas

/-! Every share held has an entry in the log that made it, what the World's sharesLogged keeps at every moment; and
every yes of viewing rests on a logged share (viewingRestsOnTheLog). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Sharing.auditTrail.Proofs
open Sharing

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro mayView record forget announce hView _ _ _ world g0 g1 g2 g3 g4 g5 g6
  exact ⟨g5, fun p d => hView p d world g0 g1 g2 g3 g4 g5 g6⟩

end Sharing.auditTrail.Proofs
