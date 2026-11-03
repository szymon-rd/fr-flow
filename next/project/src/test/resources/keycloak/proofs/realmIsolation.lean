import FrFlowGen.Keycloak.realmIsolation.Spec

/-! An introspection names the realm asking: what introspectAnswers says of every answer. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.realmIsolation.Proofs

theorem impl : Obl.impl := by
  intro lookup hA _ _ asking t world h1 h2 h3
  have h := hA asking t world h1 h2 h3
  revert h
  generalize Keycloak.introspecting_run lookup asking t world = p
  rcases p with ⟨res, aft⟩
  rintro ⟨h, -⟩ c hc
  exact (h c hc).1.1.1

end Keycloak.realmIsolation.Proofs
