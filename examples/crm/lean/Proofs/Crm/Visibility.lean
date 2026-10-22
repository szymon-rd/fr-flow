import FrFlowGen.Crm.Visibility.Spec

/-! Visibility from its parts: a search returns only stored records it asks for (SearchesMatch), each
one the user may read (NoCrossTenantRead, on whichever screen it ran); and every stored record it asks
for that the user may read (SearchesMatch). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.Visibility.Proofs
open Crm.Visibility

theorem complete : Obl.complete := by
  unfold Obl.complete
  intro history expire save read deals clock hInv hMatch
  simp only [Crm.Visibility.claim, Crm.SearchesMatch.claim, Crm.NoCrossTenantRead.claim] at *
  obtain ⟨hR, hD⟩ := hInv
  intro u q r
  obtain ⟨hsub, hall⟩ := hMatch u q
  apply propext
  constructor
  · intro hr
    refine ⟨hsub r hr, ?_⟩
    rcases q with ⟨sc, se⟩
    cases sc with
    | Records =>
      simp only [Crm.results] at hr
      have h := hR u se (u, r) (by simp only [Crm.NoCrossTenantRead.view_ReadContract, List.mem_map]; exact ⟨r, hr, rfl⟩)
      simpa [Crm.NoCrossTenantRead.rule] using h
    | Sales =>
      simp only [Crm.results] at hr
      have h := hD u se (u, r) (by simp only [Crm.NoCrossTenantRead.view_DealSearch, List.mem_map]; exact ⟨r, hr, rfl⟩)
      simpa [Crm.NoCrossTenantRead.rule] using h
  · rintro ⟨⟨hs, ha⟩, hm⟩
    exact hall r hs ⟨ha, hm⟩

end Crm.Visibility.Proofs
