import FrFlowGen.Crm.noCrossTenantRead.Spec
import Proofs.Crm.Lemmas

/-! Each screen returns only records the user may read now: what its two parts say, together. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.noCrossTenantRead.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := by
  intro fetch hR hD _ _ _ u q world h1 h2 h3
  have a := hR u q world h1 h2 h3
  have b := hD u q world h1 h2 h3
  revert a b
  generalize search_run fetch u q world = p1
  generalize dealsOf_run fetch u q world = p2
  rcases p1 with ⟨r1, a1⟩
  rcases p2 with ⟨r2, a2⟩
  exact fun a b => ⟨a, b⟩

end Crm.noCrossTenantRead.Proofs
