import FrFlowGen.Auth.grantLetsIn.Spec
import Proofs.Auth.Lemmas

/-! A request whose token's holder has a grant for the path is let in on the holder's behalf: what the decision
says when the holder has one. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Auth.grantLetsIn.Proofs

theorem complete : Obl.complete := by
  intro adm sessions grants hs hd _ t p hg
  rw [hd hs t p, ite_eq_left hg]

end Auth.grantLetsIn.Proofs
