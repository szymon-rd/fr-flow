import FrFlowGen.Keycloak.signedInAreAccepted.Spec

/-! A user signed in, and enabled, is accepted with their roles: their sign-in is a session the realm holds
(`sessionsMirrorSignIns`), the only one under its token (`oneSignInPerToken`), of an account enabled as administered
(`accountsAsAdministered`); the introspection answers for such a session (`introspectAnswers`), and what it answers
is what is accepted (`referenceTokens`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.signedInAreAccepted.Proofs

theorem complete : Obl.complete := by
  intro signedIn enabled accepted rolesOf history seed introspect state hEnabled hRoles hSigned hRef hMirror hAcc
    hOne hIntro r t u hu
  unfold accounts.claim at hEnabled
  unfold accountRoles.claim at hRoles
  unfold signInHistory.claim at hSigned
  unfold referenceTokens.claim at hRef
  unfold sessionsMirrorSignIns.claim at hMirror
  unfold accountsAsAdministered.claim at hAcc
  unfold oneSignInPerToken.claim at hOne
  unfold introspectAnswers.claim at hIntro
  obtain ⟨hs, he⟩ := hu
  rw [hSigned] at hs
  rw [hEnabled, ← hAcc] at he
  have hx : Session.mk t r u ∈ Keycloak.sessions state r := by rw [hMirror]; exact ⟨rfl, hs⟩
  have hone : onlyOne (Keycloak.sessions state r) (Session.mk t r u) := by
    intro y hy hyt
    rw [hMirror] at hy
    exact hOne y (Session.mk t r u) ⟨⟨hy.2, hs⟩, hyt⟩
  have hans := (hIntro r t).2 _ hx ⟨⟨rfl, he⟩, hone⟩
  rw [hRef, hans, hRoles, ← hAcc]
  rfl

/-- Some world meets the parts: no request yet, no account, no session, nothing accepted. -/
theorem feasible : Obl.feasible := by
  refine ⟨fun _ _ _ => False, fun _ _ => False, fun _ _ => none, fun _ _ => [], [], [], fun _ _ => none,
    ServerState.mk [] [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    simp_all [frflow_defs]

end Keycloak.signedInAreAccepted.Proofs
