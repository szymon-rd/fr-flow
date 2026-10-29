import FrFlowGen.Keycloak.Whole.Spec

/-! Keycloak's promises about the server's run, its store and the introspection hold together (owner §39). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Keycloak.Whole.Proofs

/-- A session the realm holds under the token: of the realm, under the token. -/
theorem found {state : ServerState} {realm : RealmId} {token : String} {x : Session}
    (h : (Keycloak.sessions state realm).find? (fun y => decide (y.token = token)) = some x) :
    x ∈ Keycloak.sessions state realm ∧ x.token = token ∧ x.realm = realm := by
  have hm := List.mem_of_find?_eq_some h
  have ht := List.find?_some h
  simp only [decide_eq_true_eq] at ht
  refine ⟨hm, ht, ?_⟩
  simp only [Keycloak.sessions, List.mem_filter, decide_eq_true_eq] at hm
  exact hm.2

/-- The server's promises hold together (step 12 rulings: the state the server holds is solved by `serverRun`, the
history replayed, with every statement mentioning it): a store that keeps what it is given, the state the history
leads to by `handle` over it, the step's code meeting `handleRequest` as its own proof shows; over that state, the
store's index answering from its sessions (today's `storedSession`) keeps `sessionLookup`, and an introspection
answering from that index, for a user enabled there with their roles, keeps `introspectAnswers`, its answers what
applications accept (`referenceTokens`). -/
theorem consistent_3 : Obl.consistent_3 := by
  intro history seed _
  obtain ⟨state, hrun⟩ : ∃ st, Keycloak.serverRun.claim st history seed (Keycloak.handle (fun _ after => after)) :=
    ⟨_, rfl⟩
  let lookup : RealmId → String → Option Session := fun realm token =>
    (Keycloak.sessions state realm).find? (fun y => decide (y.token = token))
  let answer : RealmId → String → Option Claims := fun realm token =>
    match (Keycloak.sessions state realm).find? (fun y => decide (y.token = token)) with
    | none => none
    | some x => if Keycloak.isEnabled (Keycloak.account state realm x.user)
        then some (Claims.mk realm x.user (Keycloak.rolesIn (Keycloak.account state realm x.user))) else none
  have hhandle : Keycloak.handleRequest.claim (Keycloak.handle (fun _ after => after)) := by frflow_auto
  have hlookup : Keycloak.sessionLookup.claim lookup state := by
    intro realm token
    refine ⟨fun x hx => ?_, fun ⟨y, hy, ht⟩ hn => ?_⟩
    · obtain ⟨hm, ht, hr⟩ := found hx
      exact ⟨⟨hm, ht⟩, hr⟩
    · rw [List.find?_eq_none] at hn
      exact hn y hy (by simpa using ht)
  have hanswer : Keycloak.introspectAnswers.claim answer state := by
    intro realm token
    refine ⟨fun c hc => ?_, fun x hx ⟨⟨ht, he⟩, hone⟩ => ?_⟩
    · simp only [answer] at hc
      split at hc
      · cases hc
      · rename_i x hx
        obtain ⟨hm, ht, hr⟩ := found hx
        split at hc
        · rename_i he
          cases hc
          have hs : Session.mk token realm x.user = x := by cases x; simp_all
          refine ⟨⟨⟨rfl, ?_⟩, he⟩, rfl⟩
          show Session.mk token realm x.user ∈ Keycloak.sessions state realm
          rw [hs]; exact hm
        · cases hc
    · have hf : (Keycloak.sessions state realm).find? (fun y => decide (y.token = token)) = some x := by
        cases hfx : (Keycloak.sessions state realm).find? (fun y => decide (y.token = token)) with
        | none =>
          rw [List.find?_eq_none] at hfx
          exact absurd (by simpa using ht) (hfx x hx)
        | some y =>
          obtain ⟨hy, hyt, _⟩ := found hfx
          exact congrArg some (hone y hy (hyt.trans ht.symm))
      simp [answer, hf, he]
  exact ⟨fun r t => Keycloak.claimsOf (answer r t), answer, fun _ after => after, lookup, state, fun _ _ => rfl,
    hrun, hhandle, fun _ _ => rfl, hanswer, hlookup⟩

end Keycloak.Whole.Proofs
