import FrFlowGen.Keycloak.answersNameASession.Spec

/-! An introspection answers only with a session the realm holds under the token: what introspectAnswers says of
every answer. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.answersNameASession.Proofs

theorem impl : Obl.impl := by
  intro lookup hA _ _ r t world h1 h2 h3
  have h := hA r t world h1 h2 h3
  revert h
  generalize Keycloak.introspecting_run lookup r t world = p
  rcases p with ⟨res, aft⟩
  rintro ⟨h, -⟩ c hc
  exact (h c hc).1.1.2

end Keycloak.answersNameASession.Proofs
