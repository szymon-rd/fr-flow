import FrFlowGen.Crm.sharedCrm.Spec
import Proofs.Crm.Lemmas

/-! A user's search finds what the screens return (`searches`), the stored records it asks for that the user may
read (`visibility`); what the CRM holds is what users added (`storeMirrorsRequests`), and a record may be read when
it is of the user's company or shared with it now, which is what users asked (`adding`, `sharing`): today's proof,
in each world meeting the database's rules. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.sharedCrm.Proofs
open Crm

theorem complete : Obl.complete := by
  intro finds asksFor added owner companyOf sharedWith read deals hC hO hS hA hAd hSh hM hV u q r world h1 h2 h3
  obtain ⟨hRec, hShared⟩ := hM world h1 h2 h3
  have hs := hS u q r world h1 h2 h3
  have hv := hV u q r world h1 h2 h3
  revert hs hv
  generalize read u q.search world = p1
  generalize deals u q.search world = p2
  rcases p1 with ⟨r1, a1⟩
  rcases p2 with ⟨r2, a2⟩
  intro hs hv
  simp only at hs hv
  rw [hs, hv, hA q r world, hO r world, hAd r.tenant r world h1 h2 h3, hC u world, hSh r u.tenant world h1 h2 h3]
  simp only [mayRead]
  rw [hRec r, hShared r.id_ u.tenant]
  apply propext
  constructor
  · rintro ⟨⟨hHeld, hAsks⟩, hMay⟩
    exact ⟨⟨hAsks, trivial, hHeld⟩, hMay⟩
  · rintro ⟨⟨hAsks, _, hHeld⟩, hMay⟩
    exact ⟨⟨hHeld, hAsks⟩, hMay⟩

/-- The parts hold together of the code: the database answering with the stored records that match, the screens
over it, and each word as its claim says. -/
theorem feasible : Obl.feasible := by
  refine ⟨fun u q r w => r ∈ onScreen q (search_run (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)) u q.search w).1 (dealsOf_run (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)) u q.search w).1,
    fun q r _ => askMatches q r, fun c r w => r.tenant = c ∧ r ∈ (askedIn w.databaseModel.events).records,
    fun r _ => r.tenant, fun a _ => a.tenant, fun r c w => sharedIn w.databaseModel.events r.id_ c w.clockModel,
    search_run (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)), dealsOf_run (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)), fun _ _ => rfl, fun _ _ => rfl, ?_, fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ => rfl, Runs.store_mirrors Runs.writes_take_effect Runs.writes_only_as_asked Runs.records_kept,
    Runs.visible (fun (_ : Account) (q : Search) (s : Tables) => (s.store.records.filter (fun r => decide («matches» q r)), s)) Runs.matching_records Runs.matching_keeps⟩
  intro u q r w _ _ _
  dsimp only

end Crm.sharedCrm.Proofs
