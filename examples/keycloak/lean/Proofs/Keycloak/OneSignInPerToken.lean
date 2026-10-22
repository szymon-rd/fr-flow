import FrFlowGen.Keycloak.OneSignInPerToken.Spec
import Proofs.Keycloak.Lemmas

/-! Authored proof that a token names one sign-in at most: two sign-ins of one history that got the same
token are the same request (the history splits at one place), or one comes before the other, and then
the later one did not carry a fresh token. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Keycloak.OneSignInPerToken.Proofs
open Keycloak Keycloak.Lemmas

/-- If a sign-in that got `x` comes before one that got `y` in a history of fresh tokens, their tokens differ. -/
theorem earlier_differs {history pre post a' : List AuthRequest} {q1 q2 : AuthRequest} {seed : List UserAccount}
    {x y : Session}
    (hf : ∀ (pre post : List AuthRequest) (q : AuthRequest), history = pre ++ q :: post → fresh pre q)
    (hh : history = (pre ++ q1 :: a') ++ q2 :: post)
    (g1 : grantedBy (accountsAfter seed pre) q1 = some x) (g2 : tokenOf q2 = some y.token) :
    x.token ≠ y.token := by
  intro heq
  have := hf _ _ _ hh
  simp only [fresh] at this
  exact this y.token g2 ⟨q1, by simp, by rw [grantedBy_token g1, heq]⟩

theorem complete : Obl.complete := by
  unfold Obl.complete
  intro history seed hFresh x y ⟨⟨hx, hy⟩, heq⟩
  simp only [Keycloak.FreshTokens.claim] at hFresh
  obtain ⟨pre1, post1, ⟨q1, h1, g1⟩, _⟩ := hx
  obtain ⟨pre2, post2, ⟨q2, h2, g2⟩, _⟩ := hy
  have hsplit : pre1 ++ q1 :: post1 = pre2 ++ q2 :: post2 := h1.symm.trans h2
  rcases List.append_eq_append_iff.1 hsplit with ⟨a', hpre, hrest⟩ | ⟨c', hpre, hrest⟩
  · cases a' with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hrest
      obtain ⟨rfl, -⟩ := hrest
      simp only [List.append_nil] at hpre
      subst hpre
      rw [g1] at g2
      exact Option.some.inj g2
    | cons a0 a'' =>
      simp only [List.cons_append, List.cons.injEq] at hrest
      obtain ⟨rfl, -⟩ := hrest
      exact absurd heq (earlier_differs hFresh (by rw [h2, hpre]) g1 (grantedBy_token g2))
  · cases c' with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hrest
      obtain ⟨rfl, -⟩ := hrest
      simp only [List.append_nil] at hpre
      subst hpre
      rw [g1] at g2
      exact Option.some.inj g2
    | cons c0 c'' =>
      simp only [List.cons_append, List.cons.injEq] at hrest
      obtain ⟨rfl, -⟩ := hrest
      exact absurd heq.symm (earlier_differs hFresh (by rw [h1, hpre]) g2 (grantedBy_token g1))

/-- Some world meets FreshTokens: a history with no request. -/
theorem feasible : Obl.feasible := by
  unfold Obl.feasible
  exact ⟨[], [], fun pre post q h => by simp at h⟩

end Keycloak.OneSignInPerToken.Proofs
