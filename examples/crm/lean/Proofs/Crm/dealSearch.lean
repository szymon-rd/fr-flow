import FrFlowGen.Crm.dealSearch.Spec
import Proofs.Crm.Lemmas

/-! The sales screen returns exactly the stored deals that match and the user may read now: what its four parts say, together. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.dealSearch.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := by
  intro fetch hM hD hR hA _ _ _ user query world h1 h2 h3
  have a := hM user query world h1 h2 h3
  have b := hD user query world h1 h2 h3
  have c := hR user query world h1 h2 h3
  have d := hA user query world h1 h2 h3
  revert a b c d
  generalize dealsOf_run fetch user query world = p
  rcases p with ⟨res, aft⟩
  exact fun a b c d => ⟨⟨⟨a, b⟩, c⟩, d⟩

end Crm.dealSearch.Proofs
