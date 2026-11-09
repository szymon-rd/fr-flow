import FrFlowGen.Keycloak.realmAccess.Spec

/-! The purpose, its two halves together: what is accepted is only what must be, and all of it. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.realmAccess.Proofs

theorem complete : Obl.complete := by
  intro accepted rolesOf signedIn enabled hNo hYes r t u w h1 h2 h3
  apply propext
  constructor
  · intro h
    have hn := hNo r t w h1 h2 h3
    exact ⟨hn.1.1 _ h, hn.1.2 _ h⟩
  · intro h
    exact hYes r t u w h1 h2 h3 h

/-- Some world meets the parts: nothing accepted, no one signed in. -/
theorem feasible : Obl.feasible := by
  refine ⟨fun _ _ _ => none, fun _ _ _ => [], fun _ _ _ _ => False, fun _ _ _ => False, ?_, ?_⟩
  · intro _ _ _ _ _ _
    exact ⟨⟨fun a ha => (by cases ha), fun a ha => (by cases ha)⟩, fun a ha => (by cases ha)⟩
  · intro _ _ _ _ _ _ _ h
    exact h.1.elim

end Keycloak.realmAccess.Proofs
