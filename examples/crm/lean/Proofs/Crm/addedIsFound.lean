import FrFlowGen.Crm.addedIsFound.Spec
import Proofs.Crm.Lemmas

/-! A record a user added, of their company, under a fresh id, is one users asked for, so one the CRM holds
(`storeMirrorsRequests`); a search returns every stored record it asks for that the user may read, as a record of
their own company is (`Runs.screened`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.addedIsFound.Proofs
open Crm Crm.Lemmas

theorem impl : Obl.impl := by
  intro fetch hM _ hR hK u r pre post q world h1 h2 h3
  have hs := Runs.screened fetch hR hK u q world ⟨h1, h2, h3⟩ r
  have hRec := (hM world h1 h2 h3).1 r
  revert hs
  generalize search_run fetch u q.search world = p1
  generalize dealsOf_run fetch u q.search world = p2
  rcases p1 with ⟨r1, a1⟩
  rcases p2 with ⟨r2, a2⟩
  intro hs hAdd hAsks
  obtain ⟨⟨hHistory, hTenant⟩, hFresh⟩ := hAdd
  have hAdded : r ∈ (askedIn (pre ++ [Event.Wrote (WriteCmd.mk u (Change.Add r))])).records := by
    rw [askedIn_snoc]
    simp only [askedStep]
    rw [ite_eq_left ⟨hTenant, hFresh⟩]
    simp
  have hNow : r ∈ (askedIn world.databaseModel.events).records := by
    have hSplit : world.databaseModel.events = (pre ++ [Event.Wrote (WriteCmd.mk u (Change.Add r))]) ++ post := by
      simp [hHistory]
    rw [hSplit]
    exact askedIn_records_append _ post hAdded
  refine hs.2 ⟨⟨hRec ▸ hNow, hAsks⟩, ?_⟩
  simp only [mayRead]
  exact Or.inl hTenant

end Crm.addedIsFound.Proofs
