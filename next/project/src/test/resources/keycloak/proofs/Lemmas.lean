import FrFlowGen.Keycloak.Domain
import FrFlowGen.Keycloak.drawnTokens.Spec
import FrFlowGen.Keycloak.storeKeepsState.Spec
import FrFlowGen.Keycloak.storeLogs.Spec
import FrFlowGen.Keycloak.lookupKeeps.Spec
import FrFlowGen.Keycloak.sessionLookup.Spec
import FrFlowGen.Keycloak.introspectAnswers.Spec
import FrFlowGen.Keycloak.loadedKept.Spec
import FrFlowGen.Keycloak.answersWhatItStores.Spec
import FrFlowGen.Keycloak.handleRequest.Spec
import FrFlowGen.Keycloak.sessionsMirrorSignIns.Spec
import FrFlowGen.Keycloak.accountsAsAdministered.Spec
import FrFlowGen.Keycloak.referenceTokens.Spec

/-! What the proofs of keycloak share: what a sign-in got and whether it still stands (`liveIn`) when one more
request comes, read as the sign-in it is; what freshness of tokens says of a prefix; the accounts after one more
request. And the server's programs on its store: each operation known only by assumptions a step of its field of the
World (`within`); what a run of the server and of the introspection leaves and answers, given what is assumed of
the store's operations: the claims on the programs, which the whole's consistency proof shows of a store too. -/

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


/-- The index's run on the World: its run on the store, the rest of the World as it was. -/
theorem lookup_run_eq (lookup : RealmId → String → StateM Stored (Option Session)) (realm : RealmId) (token : String)
    (w : World) : ServerStore.lookup_run lookup realm token w =
      ((FrFlow.runOn (lookup realm token) w.serverStore).1,
        { w with serverStore := (FrFlow.runOn (lookup realm token) w.serverStore).2 }) := rfl

/-- Storing a request, run on the World: its run on the store, the rest of the World as it was. -/
theorem record_run_eq (record : AuthRequest → ServerState → StateM Stored ServerState) (q : AuthRequest)
    (after : ServerState) (w : World) : ServerStore.record_run record q after w =
      ((FrFlow.runOn (record q after) w.serverStore).1,
        { w with serverStore := (FrFlow.runOn (record q after) w.serverStore).2 }) := rfl

/-- The next request, drawn against some handled, run on the World: its run on the inbox, the rest of the World as it
was. -/
theorem next_run_eq (nextRequest : List AuthRequest → StateM (List AuthRequest) AuthRequest)
    (handled : List AuthRequest) (w : World) : Inbox.nextRequest_run nextRequest handled w =
      ((FrFlow.runOn (nextRequest handled) w.inbox).1,
        { w with inbox := (FrFlow.runOn (nextRequest handled) w.inbox).2 }) := rfl

/-- A run of the introspection: the index's answer made claims of over the state the index's run leaves. -/
theorem introspecting_run_eq (lookup : RealmId → String → StateM Stored (Option Session)) (realm : RealmId)
    (token : String) (w : World) : introspecting_run lookup realm token w =
      ((match (FrFlow.runOn (lookup realm token) w.serverStore).1 with
        | none => none
        | some x => match accountOf (FrFlow.runOn (lookup realm token) w.serverStore).2.state.accounts realm x.user with
          | none => none
          | some a => if a.enabled then some (Claims.mk realm x.user a.roles) else none),
        { w with serverStore := (FrFlow.runOn (lookup realm token) w.serverStore).2 }) := by
  simp only [introspecting_run, introspecting, FrFlow.runOn_bind, FrFlow.runOn_pure,
    ServerStore.Ops.onState_onWorld, ServerStore.Ops.load_onWorld, FrFlow.runOn_within, ServerStore.load,
    FrFlow.runOn_get]
  rfl

/-- A run of the server: the next request taken, drawn against the log, stored with what `next` makes of the state
the store holds. -/
theorem serving_run_eq (nextRequest : List AuthRequest → StateM (List AuthRequest) AuthRequest)
    (record : AuthRequest → ServerState → StateM Stored ServerState) (w : World) :
    serving_run nextRequest record w =
      ((FrFlow.runOn (record (FrFlow.runOn (nextRequest w.serverStore.log) w.inbox).1
          (next w.serverStore.state (FrFlow.runOn (nextRequest w.serverStore.log) w.inbox).1)) w.serverStore).1,
        { w with inbox := (FrFlow.runOn (nextRequest w.serverStore.log) w.inbox).2,
                 serverStore := (FrFlow.runOn (record (FrFlow.runOn (nextRequest w.serverStore.log) w.inbox).1
                   (next w.serverStore.state (FrFlow.runOn (nextRequest w.serverStore.log) w.inbox).1))
                   w.serverStore).2 }) := by
  simp only [serving_run, serving, FrFlow.runOn_bind, FrFlow.runOn_pure, Inbox.Ops.onState_onWorld,
    ServerStore.Ops.onState_onWorld, ServerStore.Ops.load_onWorld, ServerStore.Ops.logged_onWorld,
    FrFlow.runOn_within, ServerStore.load, ServerStore.logged, FrFlow.runOn_get]

/-- The store after the server handles a request, of a store meeting its rules: the accounts as loaded, the state
`next` makes of the one it held, the request logged at the end; the request fresh against the log; the answer the
state stored. -/
theorem served (nextRequest : List AuthRequest → StateM (List AuthRequest) AuthRequest)
    (record : AuthRequest → ServerState → StateM Stored ServerState)
    (hD : drawnTokens.claim nextRequest) (hK : storeKeepsState.claim record) (hL : storeLogs.claim record)
    (w : World) (h1 : serverRun w.serverStore) (h2 : oneSignInPerToken w.serverStore)
    (h3 : freshTokens w.serverStore) :
    (serving_run nextRequest record w).2.serverStore = Stored.mk w.serverStore.loaded
        (next w.serverStore.state (FrFlow.runOn (nextRequest w.serverStore.log) w.inbox).1)
        (w.serverStore.log ++ [(FrFlow.runOn (nextRequest w.serverStore.log) w.inbox).1]) ∧
      fresh w.serverStore.log (FrFlow.runOn (nextRequest w.serverStore.log) w.inbox).1 ∧
      (serving_run nextRequest record w).1 = (serving_run nextRequest record w).2.serverStore.state := by
  have hd := hD w.serverStore.log w
  rw [next_run_eq] at hd
  let q := (FrFlow.runOn (nextRequest w.serverStore.log) w.inbox).1
  let w' : World := { w with inbox := (FrFlow.runOn (nextRequest w.serverStore.log) w.inbox).2 }
  have hl := hL q (next w.serverStore.state q) w' h1 h2 h3
  have hk := hK q (next w.serverStore.state q) w'
  rw [record_run_eq] at hl hk
  rw [serving_run_eq]
  exact ⟨hl, hd, by simp only at hl hk ⊢; rw [hk, hl]⟩

/-- The store after an introspection: as it was. -/
theorem introspected (lookup : RealmId → String → StateM Stored (Option Session)) (hK : lookupKeeps.claim lookup)
    (r : RealmId) (t : String) (w : World) (h1 : serverRun w.serverStore) (h2 : oneSignInPerToken w.serverStore)
    (h3 : freshTokens w.serverStore) : (introspecting_run lookup r t w).2.serverStore = w.serverStore := by
  have hk := hK r t w h1 h2 h3
  rw [lookup_run_eq] at hk
  rw [introspecting_run_eq]
  exact hk

/-- An introspection on an index keeping what is assumed of it answers as introspectAnswers says. -/
theorem introspect_answers (lookup : RealmId → String → StateM Stored (Option Session))
    (hS : sessionLookup.claim lookup) (hK : lookupKeeps.claim lookup) :
    introspectAnswers.claim (introspecting_run lookup) := by
  intro realm token world h1 h2 h3
  have hs := hS realm token world h1 h2 h3
  have hk := hK realm token world h1 h2 h3
  rw [lookup_run_eq] at hs hk
  simp only at hs hk
  rw [introspecting_run_eq, hk]
  simp only
  obtain ⟨hFound, hAny⟩ := hs
  revert hFound hAny
  generalize (FrFlow.runOn (lookup realm token) world.serverStore).1 = r
  intro hFound hAny
  cases r with
  | none =>
    refine ⟨fun c hc => by simp at hc, fun x hx ⟨⟨ht, _⟩, _⟩ => ?_⟩
    exact absurd rfl (hAny ⟨x, hx, ht⟩)
  | some x =>
    obtain ⟨⟨hxIn, hxt⟩, hxr⟩ := hFound x rfl
    refine ⟨fun c hc => ?_, fun y hy ⟨⟨hyt, hye⟩, hone⟩ => ?_⟩
    · simp only at hc
      split at hc
      · cases hc
      · rename_i a ha
        split at hc
        · rename_i hen
          cases hc
          refine ⟨⟨⟨rfl, ?_⟩, ⟨a, ?_, hen⟩⟩, ?_⟩
          · have hx : Session.mk token realm x.user = x := by cases x; simp_all
            simpa only [hx] using hxIn
          · simp only [account, ha]
          · simp only [rolesIn, account, ha]
        · cases hc
    · have hxy : x = y := (hone x hxIn (by rw [hxt, hyt])).symm ▸ rfl
      subst hxy
      obtain ⟨a, ha, hen⟩ := hye
      simp only [account] at ha
      simp only [ha, hen, ite_true, rolesIn, account]

/-- The server's and the introspection's runs keep the accounts as loaded. -/
theorem loaded_kept (nextRequest : List AuthRequest → StateM (List AuthRequest) AuthRequest)
    (record : AuthRequest → ServerState → StateM Stored ServerState)
    (lookup : RealmId → String → StateM Stored (Option Session))
    (hD : drawnTokens.claim nextRequest) (hK : storeKeepsState.claim record) (hL : storeLogs.claim record)
    (hLk : lookupKeeps.claim lookup) :
    loadedKept.claim (serving_run nextRequest record) (introspecting_run lookup) := by
  intro w h1 h2 h3
  refine ⟨?_, fun r t => ?_⟩
  · obtain ⟨hAfter, -, -⟩ := served nextRequest record hD hK hL w h1 h2 h3
    revert hAfter
    generalize serving_run nextRequest record w = p
    rcases p with ⟨res, aft⟩
    intro hAfter
    simp only at hAfter ⊢
    rw [hAfter]
  · have hAfter := introspected lookup hLk r t w h1 h2 h3
    revert hAfter
    generalize introspecting_run lookup r t w = p
    rcases p with ⟨res, aft⟩
    intro hAfter
    simp only at hAfter ⊢
    rw [hAfter]

/-- The server answers with the state it stores. -/
theorem answers_stored (nextRequest : List AuthRequest → StateM (List AuthRequest) AuthRequest)
    (record : AuthRequest → ServerState → StateM Stored ServerState)
    (hD : drawnTokens.claim nextRequest) (hK : storeKeepsState.claim record) (hL : storeLogs.claim record) :
    answersWhatItStores.claim (serving_run nextRequest record) := by
  intro w h1 h2 h3
  obtain ⟨-, -, hAnswer⟩ := served nextRequest record hD hK hL w h1 h2 h3
  revert hAnswer
  generalize serving_run nextRequest record w = p
  rcases p with ⟨res, aft⟩
  exact id

/-- The server's code handles a request as handleRequest says (its `impl`, proven again here). -/
theorem next_handles : handleRequest.claim next := by frflow_auto

/-- The server's sessions mirror the sign-ins that still stand: its state is its requests handled in turn by `next`
(`serverRun`), and by induction over the history (`FrFlow.tracks`) each request handled as handleRequest says of
`next` moves the sessions as one more request moves the sign-ins (`liveIn_snoc`). Fresh tokens (`freshTokens`: no two
sign-ins of the log carry one) are what make a granted sign-in open: no open session holds a token no earlier sign-in
carried. -/
theorem sessions_mirror : sessionsMirrorSignIns.claim := by
  intro r x w hRun _ hFresh
  have hStep := next_handles
  unfold handleRequest.claim at hStep
  simp only [serverRun] at hRun
  simp only [freshTokens] at hFresh
  have key := FrFlow.tracks (step := fun s q => next s q) (init := ServerState.mk w.serverStore.loaded [])
    (R := fun s es => es.Pairwise (fun p q => ∀ (t : String), tokenOf q = some t → ¬ tokenOf p = some t) →
      s.accounts = accountsAfter w.serverStore.loaded es ∧ ∀ x, x ∈ s.sessions ↔ liveIn w.serverStore.loaded es x)
    (by
      intro _
      refine ⟨by simp [accountsAfter], fun x => ?_⟩
      simp [liveIn_nil])
    (by
      intro s es e ih hf
      rw [List.pairwise_append] at hf
      obtain ⟨hf0, -, hall⟩ := hf
      have hfe : fresh es e := fun t ht ⟨p, hp, hpt⟩ => hall p hp e (List.mem_singleton_self e) t ht hpt
      simp only [fresh] at hfe
      obtain ⟨hacc, hmem⟩ := ih hf0
      obtain ⟨⟨⟨tacc, tout⟩, tkeep⟩, topen⟩ := hStep s e
      refine ⟨by rw [tacc, hacc, accountsAfter_snoc], fun x => ?_⟩
      rw [liveIn_snoc]
      constructor
      · intro hx
        rcases tout x hx with ⟨hxs, hne⟩ | ho
        · refine Or.inl ⟨(hmem x).1 hxs, ?_⟩
          rintro rfl
          exact hne (by simp [endedBy])
        · refine Or.inr ?_
          rw [← hacc]
          simp only [opened] at ho
          split at ho
          · cases ho
          · rename_i y hy
            split at ho
            · cases ho
            · cases ho; exact hy
      · rintro (⟨hl, hne⟩ | hg)
        · rcases tkeep x ((hmem x).2 hl) with he | ht
          · exfalso
            cases e with
            | SignOut r t =>
              simp only [endedBy] at he
              obtain ⟨h1, h2⟩ := he
              exact hne (by rw [h1, h2])
            | SignIn r u pw t => simp [endedBy] at he
            | SetEnabled r u on => simp [endedBy] at he
          · exact ht
        · apply topen x
          rw [← hacc] at hg
          have hnone : ¬ ∃ y ∈ s.sessions, y.token = x.token := by
            rintro ⟨y, hy, hyt⟩
            obtain ⟨p, hp, hpt⟩ := liveIn_token ((hmem y).1 hy)
            exact hfe x.token (grantedBy_token hg) ⟨p, hp, by rw [hpt, hyt]⟩
          simp only [opened, hg, hnone, ite_false])
  obtain ⟨_, hmem⟩ := key w.serverStore.log hFresh
  rw [hRun]
  apply propext
  simp only [Keycloak.sessions, Keycloak.stateAfter, List.mem_filter, decide_eq_true_eq]
  rw [hmem x]
  exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩

/-- The server holds the accounts as administered: its state is its requests handled in turn by `next`
(`serverRun`), a simulation (`FrFlow.simulates`) whose abstraction is the accounts, since each request handled
changes them as `administer` does, from the accounts loaded at start. -/
theorem accounts_administered : accountsAsAdministered.claim := by
  intro r u w hRun _ _
  simp only [serverRun] at hRun
  have h := FrFlow.simulates (step := next) (astep := administer) (α := ServerState.accounts)
    (init := ServerState.mk w.serverStore.loaded []) (ainit := w.serverStore.loaded) rfl (fun s e => rfl)
    w.serverStore.log
  rw [hRun]
  simp only [Keycloak.account, Keycloak.stateAfter, Keycloak.accountsAfter]
  rw [h]

/-- A session the realm holds under the token: of the realm, under the token. -/
theorem found {state : ServerState} {realm : RealmId} {token : String} {x : Session}
    (h : (sessions state realm).find? (fun y => decide (y.token = token)) = some x) :
    x ∈ sessions state realm ∧ x.token = token ∧ x.realm = realm := by
  have hm := List.mem_of_find?_eq_some h
  have ht := List.find?_some h
  simp only [decide_eq_true_eq] at ht
  refine ⟨hm, ht, ?_⟩
  simp only [sessions, List.mem_filter, decide_eq_true_eq] at hm
  exact hm.2

/-- An index keeping what is assumed of it: answering from the sessions the store holds (today's `storedSession`),
changing nothing. -/
theorem some_index : ∃ (lookup : RealmId → String → StateM Stored (Option Session)),
    sessionLookup.claim lookup ∧ lookupKeeps.claim lookup := by
  refine ⟨fun realm token s => ((sessions s.state realm).find? (fun y => decide (y.token = token)), s), ?_,
    fun _ _ _ _ _ _ => rfl⟩
  intro realm token w _ _ _
  rw [lookup_run_eq]
  simp only [FrFlow.runOn, StateT.run, Id.run]
  refine ⟨fun x hx => ?_, fun ⟨y, hy, ht⟩ hn => ?_⟩
  · obtain ⟨hm, ht, hr⟩ := found hx
    exact ⟨⟨hm, ht⟩, hr⟩
  · rw [List.find?_eq_none] at hn
    exact hn y hy (by simpa using ht)

/-- What applications accept, read off what an introspection answers, is what it answers. -/
theorem reference (introspect : RealmId → String → World → Option Claims × World) :
    referenceTokens.claim introspect (fun r t w => claimsOf (introspect r t w).1) := by
  intro r t w _ _ _
  generalize hp : introspect r t w = p
  rcases p with ⟨res, aft⟩
  simp only [hp]

end Keycloak.Lemmas
