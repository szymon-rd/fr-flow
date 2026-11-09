import FrFlowGen.Auth.Domain

/-! What the proofs of auth share: a token's holder. The holder is the user of a session under the token; and, when
the table issues each token to one user, the holder of a session's token is that session's user. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Auth.Lemmas

/-- The holder of a token is the user of a session under it. -/
theorem session_of_holder (sessions : Sessions) (t : String) (u : UserId) (h : holderOf sessions t = some u) :
    ∃ s ∈ sessions.open, s.token = t ∧ s.user = u := by
  unfold holderOf at h
  split at h
  · cases h
  · rename_i s hf
    cases h
    exact ⟨s, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, rfl⟩

/-- With each token issued once, the session found under a session's token is that session. -/
theorem find_session (l : List Session) (hl : l.Pairwise (fun a b => ¬a.token = b.token)) (s : Session)
    (hm : s ∈ l) : l.find? (fun x => decide (x.token = s.token)) = some s := by
  induction l with
  | nil => cases hm
  | cons y ys ih =>
    rw [List.pairwise_cons] at hl
    rcases List.mem_cons.1 hm with rfl | hm
    · simp
    · have hne : ¬y.token = s.token := hl.1 s hm
      simp only [List.find?_cons, hne, decide_false]
      exact ih hl.2 hm

/-- With each token issued once, the holder of a session's token is that session's user. -/
theorem holder_of_session (sessions : Sessions) (hs : tokensIssuedOnce sessions) (s : Session)
    (hm : s ∈ sessions.open) : holderOf sessions s.token = some s.user := by
  unfold holderOf
  rw [find_session _ hs s hm]

end Auth.Lemmas
