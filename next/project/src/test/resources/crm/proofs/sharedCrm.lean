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

end Crm.sharedCrm.Proofs
