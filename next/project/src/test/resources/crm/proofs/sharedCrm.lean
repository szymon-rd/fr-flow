import FrFlowGen.Crm.sharedCrm.Spec

/-! The purpose from its parts (today's proof): a search returns the stored records it asks for that the user may
read now (`visibility`); the CRM holds exactly the records users added, and a share as current exactly when its
company shared it so (`storeMirrorsRequests`); and the purpose's words are what their claims say. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.sharedCrm.Proofs
open Crm

theorem complete : Obl.complete := by
  intro finds asksFor added owner companyOf sharedWith read deals history clock held hk ho hC hO hS hA hAd hSh
    hM hV u q r
  obtain ⟨hRec, hShared⟩ := hM hk ho
  rw [hS u q r, hV hk ho u q r, hA q r, hO r, hAd r.tenant r, hC u, hSh r u.tenant]
  simp only [mayRead]
  rw [hRec r, hShared r.id_ u.tenant]
  apply propext
  constructor
  · rintro ⟨⟨hHeld, hAsks⟩, hMay⟩
    exact ⟨⟨hAsks, trivial, hHeld⟩, hMay⟩
  · rintro ⟨⟨hAsks, _, hHeld⟩, hMay⟩
    exact ⟨⟨hHeld, hAsks⟩, hMay⟩

/-- Some world meets the parts: no event yet, an empty store, the screens returning nothing, and each word as its
claim says. -/
theorem feasible : Obl.feasible := by
  refine ⟨fun u q r => r ∈ results (fun _ _ => []) (fun _ _ => []) u q, fun q r => askMatches q r,
    fun c r => r.tenant = c ∧ r ∈ (askedIn []).records, fun r => r.tenant, fun a => a.tenant,
    fun r c => sharedIn [] r.id_ c 0, fun _ _ => [], fun _ _ => [], [], 0, CrmStore.mk [] [] [],
    by simp [keyedTables, onePerKey], by simp [oneRowPerKey, onePerKey], fun _ => rfl, fun _ => rfl,
    fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_⟩
  · intro _ _
    simp [askedIn, sharedNow, sharedIn]
  · intro _ _ u q r
    rcases q with ⟨sc, se⟩
    cases sc <;> simp [results]

end Crm.sharedCrm.Proofs
