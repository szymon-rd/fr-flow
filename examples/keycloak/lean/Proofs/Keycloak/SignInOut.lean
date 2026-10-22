import FrFlowGen.Keycloak.SignInOut.Spec

/-! Authored proof that `step` meets SignInOut: case by case on the request, and on whether the
sign-in may open a session with a fresh token. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Keycloak.SignInOut.Proofs
open Keycloak.SignInOut

theorem impl : Obl.impl := by
  unfold Obl.impl
  intro users s q
  rcases s with ⟨o⟩
  cases q with
  | SignIn realm user hash token =>
    by_cases hc : Keycloak.mayOpen users realm user hash ∧ ¬(∃ x ∈ o, x.token = token)
    · simp only [Keycloak.step, hc]
      simp only [frflow_defs] at *
      grind
    · simp only [Keycloak.step, hc]
      simp only [frflow_defs] at *
      grind
  | SignOut realm token =>
    simp only [frflow_defs]
    grind

end Keycloak.SignInOut.Proofs
