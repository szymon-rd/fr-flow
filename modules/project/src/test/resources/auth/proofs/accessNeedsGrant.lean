import FrFlowGen.Auth.accessNeedsGrant.Spec
import Proofs.Auth.Lemmas

/-! A request is let in on behalf of a user only with a grant naming them and the path: what the decision's fold
finds comes from a session with such a grant. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Auth.accessNeedsGrant.Proofs

theorem complete : Obl.complete := by
  intro adm grants sessions hs hd t p
  cases hu : adm t p with
  | none => trivial
  | some u => exact (Lemmas.decided_from adm sessions grants hd hs t p u hu).elim fun _ h => h.2.2.2

end Auth.accessNeedsGrant.Proofs
