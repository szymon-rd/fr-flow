import FrFlowGen.Keycloak.Domain

/-! What the proofs of keycloak share: what a sign-in got and whether it still stands (`liveIn`) when one more
request comes, read as the sign-in it is; what freshness of tokens says of a prefix; the accounts after one more
request. -/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Keycloak.Lemmas

/-- A sign-in stands when the history holds a request the accounts then granted it, and no sign-out with its token
in its realm after it. -/
theorem liveIn_iff (seed : List UserAccount) (hs : List AuthRequest) (x : Session) :
    liveIn seed hs x ↔ ∃ pre q post, hs = pre ++ q :: post ∧ grantedBy (accountsAfter seed pre) q = some x ∧
      AuthRequest.SignOut x.realm x.token ∉ post := by
  simp only [liveIn, Classical.not_forall, Classical.not_not, and_assoc]

/-- A history whose every sign-in carries a new token stays so without its last request, and that request is fresh
after the others. -/
theorem fresh_snoc {es : List AuthRequest} {e : AuthRequest}
    (h : ∀ (pre : List AuthRequest) (q : AuthRequest) (post : List AuthRequest), es ++ [e] = pre ++ q :: post →
      fresh pre q) :
    (∀ (pre : List AuthRequest) (q : AuthRequest) (post : List AuthRequest), es = pre ++ q :: post → fresh pre q) ∧
      fresh es e := by
  constructor
  · intro pre q post hq
    exact h pre q (post ++ [e]) (by simp [hq])
  · exact h es e [] (by simp)

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
  rw [liveIn_iff]
  rintro ⟨pre, q, post, h, _⟩
  simp at h

/-- A session that still stands was got by a sign-in of the history, which carried its token. -/
theorem liveIn_token {seed : List UserAccount} {hs : List AuthRequest} {x : Session}
    (h : liveIn seed hs x) : ∃ p ∈ hs, tokenOf p = some x.token := by
  obtain ⟨pre, q, post, hq, hg, _⟩ := (liveIn_iff seed hs x).1 h
  exact ⟨q, by simp [hq], grantedBy_token hg⟩

/-- The accounts after one more request: that request's change applied to the accounts before it. -/
theorem accountsAfter_snoc (seed : List UserAccount) (es : List AuthRequest) (e : AuthRequest) :
    accountsAfter seed (es ++ [e]) = administer (accountsAfter seed es) e := by
  simp [accountsAfter, List.foldl_append]

/-- A sign-in stands after one more request exactly when it stood before and that request is not a sign-out with its
token in its realm, or that request is the sign-in, granted by the accounts then. -/
theorem liveIn_snoc (seed : List UserAccount) (es : List AuthRequest) (e : AuthRequest) (x : Session) :
    liveIn seed (es ++ [e]) x ↔
      (liveIn seed es x ∧ e ≠ AuthRequest.SignOut x.realm x.token) ∨
        grantedBy (accountsAfter seed es) e = some x := by
  rw [liveIn_iff, liveIn_iff]
  constructor
  · rintro ⟨pre, q, post, hq, hg, hno⟩
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
      exact Or.inl ⟨⟨pre, q, L, rfl, hg, hno.1⟩, fun h => hno.2 h.symm⟩
  · rintro (⟨⟨pre, q, post, hq, hg, hno⟩, he⟩ | hg)
    · refine ⟨pre, q, post ++ [e], by simp [hq], hg, ?_⟩
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨hno, fun h => he h.symm⟩
    · exact ⟨es, e, [], by simp, hg, by simp⟩

end Keycloak.Lemmas
