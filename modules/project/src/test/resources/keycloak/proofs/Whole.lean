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
  obtain ⟨lookup, hS, hLk⟩ := Lemmas.some_index
  let storing : AuthRequest → ServerState → StateM Stored ServerState :=
    fun q after s => (after, Stored.mk s.loaded after (s.log ++ [q]))
  have hK : storeKeepsState.claim storing := fun q a w => rfl
  have hL : storeLogs.claim storing := fun q a w _ _ _ => rfl
  exact ⟨_, storing, fun r t w => claimsOf (introspecting_run lookup r t w).1, lookup, signing_in_drawn, hK, hL,
    Lemmas.reference (introspecting_run lookup), Lemmas.introspect_answers lookup hS hLk, hS, hLk,
    Lemmas.loaded_kept _ storing lookup signing_in_drawn hK hL hLk,
    Lemmas.answers_stored _ storing signing_in_drawn hK hL⟩

end Keycloak.Whole.Proofs
