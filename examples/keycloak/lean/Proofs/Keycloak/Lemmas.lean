import FrFlowGen.Keycloak.Domain

/-! Facts about the history of requests, shared by the authored proofs: what a sign-in got and whether
it still stands (`liveIn`) when one more request comes, and what freshness of tokens says of a prefix. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Keycloak.Lemmas
open Keycloak

/-- A request is fresh in a history whose every sign-in carries a new token: such a history stays so
without its last request, and that request is fresh after the others. -/
theorem fresh_snoc {es : List AuthRequest} {e : AuthRequest}
    (h : ∀ (pre post : List AuthRequest) (q : AuthRequest), es ++ [e] = pre ++ q :: post → fresh pre q) :
    (∀ (pre post : List AuthRequest) (q : AuthRequest), es = pre ++ q :: post → fresh pre q) ∧ fresh es e := by
  constructor
  · intro pre post q hq
    exact h pre (post ++ [e]) q (by simp [hq])
  · exact h es [] e (by simp)

/-- The session a granted sign-in gets carries the sign-in's token. -/
theorem grantedBy_token {as : List UserAccount} {q : AuthRequest} {x : Session}
    (h : grantedBy as q = some x) : tokenOf q = some x.token := by
  cases q with
  | SignIn r u pw t =>
    simp only [grantedBy] at h
    split at h
    · cases h; rfl
    · cases h
  | SignOut r t => simp [grantedBy] at h
  | SetEnabled r u on => simp [grantedBy] at h

/-- Nothing has been signed in to before any request. -/
theorem liveIn_nil {seed : List UserAccount} {x : Session} : ¬ liveIn seed [] x := by
  rintro ⟨pre, post, ⟨q, h, _⟩, _⟩
  simp at h

/-- A session that still stands was got by a sign-in of the history, which carried its token. -/
theorem liveIn_token {seed : List UserAccount} {hs : List AuthRequest} {x : Session}
    (h : liveIn seed hs x) : ∃ p ∈ hs, tokenOf p = some x.token := by
  obtain ⟨pre, post, ⟨q, hq, hg⟩, _⟩ := h
  exact ⟨q, by simp [hq], grantedBy_token hg⟩

/-- The accounts after one more request: that request's change applied to the accounts before it. -/
theorem accountsAfter_snoc (seed : List UserAccount) (es : List AuthRequest) (e : AuthRequest) :
    accountsAfter seed (es ++ [e]) = administer (accountsAfter seed es) e := by
  simp [accountsAfter, List.foldl_append]

/-- A sign-in stands after one more request exactly when it stood before and that request is not a
sign-out with its token in its realm, or that request is the sign-in, granted by the accounts then. -/
theorem liveIn_snoc (seed : List UserAccount) (es : List AuthRequest) (e : AuthRequest) (x : Session) :
    liveIn seed (es ++ [e]) x ↔
      (liveIn seed es x ∧ e ≠ AuthRequest.SignOut x.realm x.token) ∨ grantedBy (accountsAfter seed es) e = some x := by
  constructor
  · rintro ⟨pre, post, ⟨q, hq, hg⟩, hno⟩
    rcases List.eq_nil_or_concat post with rfl | ⟨L, b, rfl⟩
    · have hq' : es ++ [e] = pre ++ [q] := hq
      obtain ⟨rfl, he⟩ := List.append_inj' hq' rfl
      have he' : e = q := by simpa using he
      subst he'
      exact Or.inr hg
    · have hq' : es ++ [e] = (pre ++ q :: L) ++ [b] := by simpa using hq
      obtain ⟨rfl, he⟩ := List.append_inj' hq' rfl
      have he' : e = b := by simpa using he
      subst he'
      simp only [List.concat_eq_append, List.mem_append, List.mem_singleton, not_or] at hno
      exact Or.inl ⟨⟨pre, L, ⟨q, rfl, hg⟩, hno.1⟩, fun h => hno.2 h.symm⟩
  · rintro (⟨⟨pre, post, ⟨q, hq, hg⟩, hno⟩, he⟩ | hg)
    · refine ⟨pre, post ++ [e], ⟨q, by simp [hq], hg⟩, ?_⟩
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨hno, fun h => he h.symm⟩
    · exact ⟨es, [], ⟨e, by simp, hg⟩, by simp⟩

end Keycloak.Lemmas
