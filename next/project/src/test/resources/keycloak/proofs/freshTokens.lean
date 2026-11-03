import FrFlowGen.Keycloak.freshTokens.Spec
import Proofs.Keycloak.Lemmas

/-! No two sign-ins of the log carry one token, kept by the server's code: the request it logs carries a token no
sign-in of the log carried (`drawnTokens`), logged at the end (`storeLogs`); an introspection changes nothing. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.freshTokens.Proofs
open Keycloak

theorem cover_serve : Obl.cover_serve := by
  intro nextRequest record hD hK hL w h1 h2 h3
  obtain ⟨hAfter, hFresh, -⟩ := Lemmas.served nextRequest record hD hK hL w h1 h2 h3
  revert hAfter
  generalize serving_run nextRequest record w = p
  rcases p with ⟨res, aft⟩
  intro hAfter
  simp only at hAfter ⊢
  rw [hAfter]
  simp only [freshTokens, List.pairwise_append, List.pairwise_singleton, List.mem_singleton, forall_eq] at h3 ⊢
  refine ⟨h3, trivial, fun p hp t ht htp => ?_⟩
  exact hFresh t ht ⟨p, hp, htp⟩

theorem cover_introspect : Obl.cover_introspect := by
  intro lookup _ hK r t w h1 h2 h3
  have hAfter := Lemmas.introspected lookup hK r t w h1 h2 h3
  revert hAfter
  generalize introspecting_run lookup r t w = p
  rcases p with ⟨res, aft⟩
  intro hAfter
  simp only at hAfter ⊢
  rw [hAfter]
  exact h3

end Keycloak.freshTokens.Proofs
