import FrFlowGen.Crm.readContract.Spec
import Proofs.Crm.Lemmas

/-! The records screen returns exactly the stored records that match and the user may read now: what its three parts say, together. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.readContract.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := by
  intro fetch hM hR hA _ _ _ user query world h1 h2 h3
  have a := hM user query world h1 h2 h3
  have b := hR user query world h1 h2 h3
  have c := hA user query world h1 h2 h3
  revert a b c
  generalize search_run fetch user query world = p
  rcases p with ⟨res, aft⟩
  exact fun a b c => ⟨⟨a, b⟩, c⟩

end Crm.readContract.Proofs
