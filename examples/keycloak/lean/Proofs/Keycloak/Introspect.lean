import FrFlowGen.Keycloak.Introspect.Spec

/-! Authored proof that `introspection` meets Introspect, from what the store's index promises
(SessionLookup): the session it returns is held under the token in the realm asked, and when the token
names only one such session, it is that one. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Keycloak.Introspect.Proofs
open Keycloak

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro history step seed lookup hLook hStep
  simp only [Keycloak.SessionLookup.claim, Keycloak.SessionLookup.post] at hLook
  simp only [Keycloak.Introspect.claim, Keycloak.Introspect.post, Keycloak.introspection]
  intro realm token
  obtain ⟨hsome, hdef⟩ := hLook realm token
  constructor
  · intro c hc
    cases hlk : lookup realm token with
    | none => simp [hlk] at hc
    | some x =>
      obtain ⟨⟨hxs, hxt⟩, hxr⟩ := hsome x hlk
      simp only [hlk] at hc
      split at hc
      · rename_i hen
        simp only [Option.some.injEq] at hc
        subst hc
        have hx : Session.mk token realm x.user = x := by
          obtain ⟨xt, xr, xu⟩ := x
          simp only at hxt hxr
          simp [hxt, hxr]
        exact ⟨⟨⟨rfl, by rw [hx]; exact hxs⟩, hen⟩, rfl⟩
      · cases hc
  · intro x hx ⟨⟨hxt, hen⟩, hone⟩
    cases hlk : lookup realm token with
    | none => exact absurd hlk (hdef ⟨x, hx, hxt⟩)
    | some y =>
      obtain ⟨⟨hys, hyt⟩, _⟩ := hsome y hlk
      have hyx : y = x := hone y hys (by rw [hyt, hxt])
      subst hyx
      simp [hen]

end Keycloak.Introspect.Proofs
