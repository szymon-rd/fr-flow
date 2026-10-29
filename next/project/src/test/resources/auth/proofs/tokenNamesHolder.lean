import FrFlowGen.Auth.tokenNamesHolder.Spec
import Proofs.Auth.Lemmas

/-! A request is let in only on behalf of the user its token was issued to: what the decision's fold finds comes
from a session under the token. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Auth.tokenNamesHolder.Proofs

theorem complete : Obl.complete := by
  intro adm sessions grants hs hd _ t p
  cases hu : adm t p with
  | none => trivial
  | some u =>
    obtain ⟨s, hm, ht, hsu, _⟩ := Lemmas.decided_from adm sessions grants hd hs t p u hu
    exact ⟨s, hm, ht, hsu⟩

end Auth.tokenNamesHolder.Proofs
