import FrFlowGen.Keycloak.oneSignInPerToken.Spec
import Proofs.Keycloak.Lemmas

/-! Two sign-ins that still stand never share a token, kept by the server's code: one request on, a sign-in stands
when it stood before or is the request, granted (`liveIn_snoc`); two that stood before are one, as before; the
request's token is its own (`grantedBy_token`) and no sign-in that stood before carried it (`drawnTokens`, each
standing sign-in carried by the log, `liveIn_token`); and the request grants one session at most. An introspection
changes nothing. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.oneSignInPerToken.Proofs
open Keycloak

/-- One stood before, the other is the request's: they share no token. -/
theorem apart {loaded : List UserAccount} {log : List AuthRequest} {q : AuthRequest} {x y : Session}
    (hFresh : fresh log q) (hx : liveIn loaded log x) (hy : grantedBy (accountsAfter loaded log) q = some y)
    (ht : x.token = y.token) : False := by
  obtain ⟨p, hp, hpt⟩ := Lemmas.liveIn_token hx
  exact hFresh y.token (Lemmas.grantedBy_token hy) ⟨p, hp, by rw [hpt, ht]⟩

theorem cover_serve : Obl.cover_serve := by
  intro nextRequest record hD hK hL w h1 h2 h3
  obtain ⟨hAfter, hFresh, -⟩ := Lemmas.served nextRequest record hD hK hL w h1 h2 h3
  revert hAfter
  generalize serving_run nextRequest record w = p
  rcases p with ⟨res, aft⟩
  intro hAfter
  simp only at hAfter ⊢
  rw [hAfter]
  intro x y ⟨⟨hx, hy⟩, ht⟩
  rw [Lemmas.liveIn_snoc] at hx hy
  rcases hx with ⟨hx, _⟩ | hx <;> rcases hy with ⟨hy, _⟩ | hy
  · exact h2 x y ⟨⟨hx, hy⟩, ht⟩
  · exact (apart hFresh hx hy ht).elim
  · exact (apart hFresh hy hx ht.symm).elim
  · rw [hx] at hy
    exact Option.some.inj hy

theorem cover_introspect : Obl.cover_introspect := by
  intro lookup _ hK r t w h1 h2 h3
  have hAfter := Lemmas.introspected lookup hK r t w h1 h2 h3
  revert hAfter
  generalize introspecting_run lookup r t w = p
  rcases p with ⟨res, aft⟩
  intro hAfter
  simp only at hAfter ⊢
  rw [hAfter]
  exact h2

end Keycloak.oneSignInPerToken.Proofs
