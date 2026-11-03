import FrFlowGen.Keycloak.serverRun.Spec
import Proofs.Keycloak.Lemmas

/-! The server's state is what its requests led to, kept by its code: handling a request stores what `next` makes of
the state it held, the request logged at the end (`storeLogs`), which is the history one request on; an
introspection changes nothing the store holds (`lookupKeeps`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.serverRun.Proofs
open Keycloak

theorem cover_serve : Obl.cover_serve := by
  intro nextRequest record hD hK hL w h1 h2 h3
  obtain ⟨hAfter, -, -⟩ := Lemmas.served nextRequest record hD hK hL w h1 h2 h3
  revert hAfter
  generalize serving_run nextRequest record w = p
  rcases p with ⟨res, aft⟩
  intro hAfter
  simp only at hAfter ⊢
  rw [hAfter]
  simp only [serverRun, stateAfter, List.foldl_append, List.foldl_cons, List.foldl_nil] at h1 ⊢
  rw [h1]

theorem cover_introspect : Obl.cover_introspect := by
  intro lookup _ hK r t w h1 h2 h3
  have hAfter := Lemmas.introspected lookup hK r t w h1 h2 h3
  revert hAfter
  generalize introspecting_run lookup r t w = p
  rcases p with ⟨res, aft⟩
  intro hAfter
  simp only at hAfter ⊢
  rw [hAfter]
  exact h1

end Keycloak.serverRun.Proofs
