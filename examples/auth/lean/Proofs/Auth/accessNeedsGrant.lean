import FrFlowGen.Auth.accessNeedsGrant.Spec
import Proofs.Auth.Lemmas

/-! A request is let in on behalf of a user only with a grant naming them and the path: the decision lets in the
token's holder only when they have one. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Auth.accessNeedsGrant.Proofs

theorem complete : Obl.complete := by
  intro adm grants sessions hs hd t p u hu
  rw [hd hs t p] at hu
  split at hu
  · rename_i hg
    unfold holderGranted at hg
    obtain ⟨v, hv, hgv⟩ := hg
    rw [hv] at hu
    cases hu
    exact hgv
  · cases hu

end Auth.accessNeedsGrant.Proofs
