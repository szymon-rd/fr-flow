import FrFlowGen.Keycloak.noUnauthorizedAccess.Spec

/-! No unauthorized access, its three rules together. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.noUnauthorizedAccess.Proofs

theorem complete : Obl.complete := by
  intro accepted signedIn enabled rolesOf hOnly hDis hRoles r t w h1 h2 h3
  exact ⟨⟨hOnly r t w h1 h2 h3, hDis r t w h1 h2 h3⟩, hRoles r t w h1 h2 h3⟩

/-- Some world meets the parts: nothing accepted. -/
theorem feasible : Obl.feasible := by
  refine ⟨fun _ _ _ => none, fun _ _ _ _ => False, fun _ _ _ => False, fun _ _ _ => [], ?_, ?_, ?_⟩
  all_goals
    intro _ _ _ _ _ _ a ha
    cases ha

end Keycloak.noUnauthorizedAccess.Proofs
