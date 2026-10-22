import FrFlowGen.Keycloak.OnlyTheSignedIn.Spec

/-! Authored proof that a token is accepted only as the user who signed in with it: the answer names a
session the realm asking holds (AnswersNameASession, RealmIsolation), and a session held is a sign-in
that still stands (SessionsMirrorSignIns). -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Keycloak.OnlyTheSignedIn.Proofs
open Keycloak

theorem complete : Obl.complete := by
  unfold Obl.complete
  intro introspect history seed step hIso hAns hMirror
  simp only [Keycloak.RealmIsolation.claim, Keycloak.AnswersNameASession.claim,
    Keycloak.SessionsMirrorSignIns.claim] at hIso hAns hMirror
  simp only [Keycloak.OnlyTheSignedIn.claim, Keycloak.accepted, Keycloak.signedIn, Keycloak.claimsOf]
  intro r t a ha
  cases hc : introspect r t with
  | none => simp [hc] at ha
  | some c =>
    simp only [hc, Option.some.injEq] at ha
    subst ha
    have hr : c.realm = r := by
      have := hIso r t (r, c) (by simp [Keycloak.RealmIsolation.view_Introspect, hc])
      simpa [Keycloak.RealmIsolation.rule] using this
    have hx := hAns r t c hc
    rw [hMirror] at hx
    rw [← hr]
    exact hx.2

end Keycloak.OnlyTheSignedIn.Proofs
