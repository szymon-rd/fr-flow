import FrFlowGen.Auth.tokenNamesHolder.Spec
import Proofs.Auth.Lemmas

/-! A request is let in only on behalf of the user its token was issued to: the decision lets in only the token's
holder. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Auth.tokenNamesHolder.Proofs

theorem complete : Obl.complete := by
  intro adm sessions grants hs hd _ t p u hu
  rw [hd hs t p] at hu
  split at hu
  · exact Lemmas.issued_of_holder sessions t u hu
  · cases hu

end Auth.tokenNamesHolder.Proofs
