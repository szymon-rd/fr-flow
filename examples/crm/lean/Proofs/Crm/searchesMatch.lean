import FrFlowGen.Crm.searchesMatch.Spec
import Proofs.Crm.Lemmas

/-! Either screen returns exactly the stored records it asks for and the user may read (`Runs.screened`), so only stored records it asks for, and every one the user may read. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.searchesMatch.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := by
  intro fetch _ _ hR hK u q world h1 h2 h3
  have hs := Runs.screened fetch hR hK u q world ⟨h1, h2, h3⟩
  revert hs
  generalize search_run fetch u q.search world = p1
  generalize dealsOf_run fetch u q.search world = p2
  rcases p1 with ⟨r1, a1⟩
  rcases p2 with ⟨r2, a2⟩
  intro hs
  exact ⟨fun r h => ((hs r).1 h).1, fun r hr hm => (hs r).2 ⟨⟨hr, hm.1⟩, hm.2⟩⟩

end Crm.searchesMatch.Proofs
