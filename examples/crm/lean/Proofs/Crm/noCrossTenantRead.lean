import FrFlowGen.Crm.noCrossTenantRead.Spec
import Proofs.Crm.Lemmas

/-! Each screen returns only records the user may read now (`Runs.searched`, `Runs.dealt`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.noCrossTenantRead.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := by
  intro fetch _ _ hR hK u q world h1 h2 h3
  have hs := (Runs.searched fetch hR hK u q world ⟨h1, h2, h3⟩).2
  have hd := (Runs.dealt fetch hR hK u q world ⟨h1, h2, h3⟩).2
  revert hs hd
  generalize search_run fetch u q world = p1
  generalize dealsOf_run fetch u q world = p2
  rcases p1 with ⟨r1, a1⟩
  rcases p2 with ⟨r2, a2⟩
  intro hs hd
  exact ⟨fun r h => ((hs r).1 h).2, fun r h => ((hd r).1 h).2⟩

end Crm.noCrossTenantRead.Proofs
