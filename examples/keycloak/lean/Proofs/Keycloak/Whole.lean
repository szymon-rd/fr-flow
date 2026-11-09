import FrFlowGen.Keycloak.Whole.Spec
import Proofs.Keycloak.Lemmas

/-! What is assumed of the server's store and of the requests it is handed, and what its programs are claimed to do,
hold together (owner §39): a store that keeps what it is given and logs the request (today's `storedAs`), an index
answering from the sessions the store holds (today's `storedSession`, `Lemmas.some_index`), changing nothing; an HTTP
API handing on a sign-in each time, its token longer than any the requests it is shown carry (so a request does
carry a token: `drawn_signs_in`); and what applications accept, what the introspection answers. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.Whole.Proofs
open Keycloak

/-- Each string of a list no longer than the longest. -/
theorem le_longest (toks : List String) :
    ∀ t ∈ toks, t.length ≤ toks.foldr (fun s m => max s.length m) 0 := by
  induction toks with
  | nil => intro t ht; cases ht
  | cons x xs ih =>
    intro t ht
    simp only [List.foldr_cons]
    cases ht with
    | head => exact Nat.le_max_left _ _
    | tail _ h' => exact Nat.le_trans (ih t h') (Nat.le_max_right _ _)

/-- An HTTP API handing on a sign-in each time, its token longer than any the requests it is shown carry, meets what
is assumed of the draw. -/
theorem signing_in_drawn : drawnTokens.claim ((fun pre inbox => (AuthRequest.SignIn (RealmId.mk "") "" ""
    (String.ofList (List.replicate ((pre.filterMap tokenOf).foldr (fun s m => max s.length m) 0 + 1) 'a')),
    inbox)) : List AuthRequest → StateM (List AuthRequest) AuthRequest) := by
  intro handled w
  rw [Lemmas.next_run_eq]
  intro t ht ⟨p, hp, hpt⟩
  simp only [FrFlow.runOn, StateT.run, Id.run, tokenOf, Option.some.injEq] at ht
  subst ht
  have := le_longest _ _ (List.mem_filterMap.2 ⟨p, hp, hpt⟩)
  simp at this
  omega

/-- What is assumed of the draw lets a request carry a token: an API meeting it hands on a sign-in, from every
inbox, against every log. -/
theorem drawn_signs_in : ∃ nextRequest, drawnTokens.claim nextRequest ∧
    ∀ handled inbox, (tokenOf (FrFlow.runOn (nextRequest handled) inbox).1).isSome :=
  ⟨_, signing_in_drawn, fun _ _ => rfl⟩

theorem consistent_3 : Obl.consistent_3 := by
  obtain ⟨lookup, hO, hF, hLk⟩ := Lemmas.some_index
  let storing : AuthRequest → ServerState → StateM Stored ServerState :=
    fun q after s => (after, Stored.mk s.loaded after (s.log ++ [q]))
  have hK : storeKeepsState.claim storing := fun q a w => rfl
  have hH : storeHoldsState.claim storing := fun q a w _ _ _ => rfl
  have hA : storeAppendsLog.claim storing := fun q a w _ _ _ => rfl
  have hKL : storeKeepsLoaded.claim storing := fun q a w _ _ _ => rfl
  exact ⟨_, storing, fun r t w => claimsOf (introspecting_run lookup r t w).1, lookup, signing_in_drawn, hK, hH, hA,
    hKL, Lemmas.reference (introspecting_run lookup), Lemmas.isolated lookup hO hF hLk,
    Lemmas.names_session lookup hO hF hLk, Lemmas.only_enabled lookup hO hF hLk, Lemmas.with_roles lookup hO hF hLk,
    Lemmas.the_session lookup hO hF hLk, hO, hF, hLk,
    Lemmas.loaded_kept _ storing lookup signing_in_drawn hK hH hA hKL hLk,
    Lemmas.answers_stored _ storing signing_in_drawn hK hH hA hKL⟩

/-- A store that starts as loaded: the accounts loaded and no session, an empty log. -/
theorem fresh_store {s : Stored} (h : storeStarts s) : ∃ l, s = Stored.mk l (ServerState.mk l []) [] := by
  obtain ⟨l, st, lg⟩ := s
  simp only [storeStarts, freshStore, Stored.mk.injEq] at h
  obtain ⟨-, rfl, rfl⟩ := h
  exact ⟨l, rfl⟩

/-! The store's rules hold where it starts. FrFlow's own try, rewriting the store with what starts it, which names the
store again, does not end. -/

theorem start_serverRun : Obl.start_serverRun := by
  intro s h
  obtain ⟨l, rfl⟩ := fresh_store h
  simp [serverRun, stateAfter]

theorem start_oneSignInPerToken : Obl.start_oneSignInPerToken := by
  intro s h
  obtain ⟨l, rfl⟩ := fresh_store h
  intro x y hxy
  exact absurd hxy.1.1 Lemmas.liveIn_nil

theorem start_freshTokens : Obl.start_freshTokens := by
  intro s h
  obtain ⟨l, rfl⟩ := fresh_store h
  exact List.Pairwise.nil

end Keycloak.Whole.Proofs
