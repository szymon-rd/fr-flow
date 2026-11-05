import FrFlowGen.Auth.grantLetsIn.Spec
import Proofs.Auth.Lemmas

/-! A request whose token was issued to a user with a grant for the path is let in on their behalf: the table issues
each token to one user, so the decision's fold finds that session. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Auth.grantLetsIn.Proofs

theorem complete : Obl.complete := by
  intro sessions adm grants hs hd _ t p s hm ht hg
  exact Lemmas.decided_finds adm sessions grants hd hs t p s hm ht hg

end Auth.grantLetsIn.Proofs
