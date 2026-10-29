import FrFlowGen.Auth.Domain
import FrFlowGen.Auth.decisionContract.Spec

/-! What the proofs of auth share: the decision's fold over the session table, read both ways. A request is let in
on behalf of a user only when a session under its token names them and a grant names them and the path; and, when
the table issues each token to one user, the session under the token with a grant is the one let in. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Auth.Lemmas

/-- What the fold finds comes from where it started, or from a session it went over under the token, with a grant. -/
theorem found_from (grants : List Grant) (token : String) (path : Path) (u : UserId) :
    ∀ (l : List Session) (init : Option UserId),
      l.foldl (fun (found : Option UserId) (s : Session) =>
        if s.token = token ∧ grantFor grants s.user path then some s.user else found) init = some u →
      init = some u ∨ ∃ s ∈ l, s.token = token ∧ s.user = u ∧ grantFor grants u path := by
  intro l
  induction l with
  | nil => intro init h; exact Or.inl h
  | cons x xs ih =>
    intro init h
    rcases ih _ h with h1 | ⟨s, hs, ht, hu, hg⟩
    · dsimp only at h1
      split at h1
      · rename_i hc
        cases h1
        exact Or.inr ⟨x, List.mem_cons_self, hc.1, rfl, hc.2⟩
      · exact Or.inl h1
    · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs, ht, hu, hg⟩

/-- Over sessions none of which is under the token with a grant, the fold keeps what it started with. -/
theorem keeps (grants : List Grant) (token : String) (path : Path) :
    ∀ (l : List Session) (init : Option UserId),
      (∀ y ∈ l, ¬(y.token = token ∧ grantFor grants y.user path)) →
      l.foldl (fun (found : Option UserId) (s : Session) =>
        if s.token = token ∧ grantFor grants s.user path then some s.user else found) init = init := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons x xs ih =>
    intro init h
    simp only [List.foldl_cons]
    rw [ite_eq_right (h x List.mem_cons_self)]
    exact ih init (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- With each token issued once, the session under the token with a grant is the one the fold finds. -/
theorem finds (grants : List Grant) (token : String) (path : Path) :
    ∀ (l : List Session) (init : Option UserId), l.Pairwise (fun a b => ¬a.token = b.token) →
      ∀ s ∈ l, s.token = token → grantFor grants s.user path →
      l.foldl (fun (found : Option UserId) (s : Session) =>
        if s.token = token ∧ grantFor grants s.user path then some s.user else found) init = some s.user := by
  intro l
  induction l with
  | nil => intro _ _ s hs; simp at hs
  | cons x xs ih =>
    intro init hp s hs ht hg
    rw [List.pairwise_cons] at hp
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hs with rfl | hs
    · rw [ite_eq_left ⟨ht, hg⟩]
      exact keeps grants token path xs _ (fun y hy hc => hp.1 y hy (ht.trans hc.1.symm))
    · exact ih _ hp.2 s hs ht hg

/-- The decision lets a request in on behalf of a user only for a session of theirs under its token, with a grant
naming them and the path. -/
theorem decided_from (adm : String → Path → Option UserId) (sessions : Sessions) (grants : List Grant)
    (h : decisionContract.claim adm sessions grants) (hs : tokensIssuedOnce sessions) (t : String) (p : Path)
    (u : UserId) (hu : adm t p = some u) :
    ∃ s ∈ sessions.open, s.token = t ∧ s.user = u ∧ grantFor grants u p := by
  unfold decisionContract.claim at h
  rw [h hs t p] at hu
  rcases found_from grants t p u _ _ hu with h0 | found
  · cases h0
  · exact found

/-- With each token issued once, the decision lets in the user of the session under the token, with a grant. -/
theorem decided_finds (adm : String → Path → Option UserId) (sessions : Sessions) (grants : List Grant)
    (h : decisionContract.claim adm sessions grants) (hs : tokensIssuedOnce sessions) (t : String) (p : Path)
    (s : Session) (hm : s ∈ sessions.open) (ht : s.token = t) (hg : grantFor grants s.user p) :
    adm t p = some s.user := by
  unfold decisionContract.claim at h
  rw [h hs t p]
  exact finds grants t p _ none hs s hm ht hg

end Auth.Lemmas
