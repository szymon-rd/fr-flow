import FrFlowGen.Keycloak.Introspect.Spec

/-! Authored proof of Introspect's expectation: an answer names a stored session of the token, so a
token with no stored session gets no answer. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Keycloak.Introspect.Proofs
open Keycloak.Introspect

theorem expect_0 : Obl.expect_0 := by
  unfold Obl.expect_0
  intro sessionsByToken users lookup m h r t hn
  simp only [frflow_defs] at *
  cases hm : m r t with
  | none => rfl
  | some c =>
    have := ((h r t).1 c hm).1.2
    simp [hn] at this

end Keycloak.Introspect.Proofs
