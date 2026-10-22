import FrFlowGen.Keycloak.SignedInAreAccepted.Spec

/-! Authored proof that a user signed in, and enabled, is accepted with their roles: their sign-in is a
session the realm holds (SessionsMirrorSignIns), the only one under its token (OneSignInPerToken), of an
account enabled as administered (AccountsAsAdministered); Introspect answers for such a session. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Keycloak.SignedInAreAccepted.Proofs
open Keycloak

theorem complete : Obl.complete := by
  unfold Obl.complete
  intro history seed introspect step hMirror hAcc hOne hIntro
  simp only [Keycloak.SessionsMirrorSignIns.claim, Keycloak.AccountsAsAdministered.claim,
    Keycloak.OneSignInPerToken.claim, Keycloak.Introspect.claim, Keycloak.Introspect.post] at hMirror hAcc hOne hIntro
  simp only [Keycloak.SignedInAreAccepted.claim, Keycloak.accepted, Keycloak.signedIn, Keycloak.enabled,
    Keycloak.rolesOf, Keycloak.claimsOf]
  intro r t u ⟨hlive, hen⟩
  have hx : Session.mk t r u ∈ Keycloak.sessions history step seed r := by
    rw [hMirror]; exact ⟨rfl, hlive⟩
  have hone : onlyOne (Keycloak.sessions history step seed r) (Session.mk t r u) := by
    intro y hy hyt
    rw [hMirror] at hy
    exact hOne y (Session.mk t r u) ⟨⟨hy.2, hlive⟩, hyt⟩
  have hen' : isEnabled (Keycloak.account history step seed r u) := by rw [hAcc]; exact hen
  have hans := (hIntro r t).2 _ hx ⟨⟨rfl, hen'⟩, hone⟩
  rw [hans, hAcc]

end Keycloak.SignedInAreAccepted.Proofs
