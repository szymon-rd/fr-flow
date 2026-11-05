import FrFlowGen.Old.RealmAccess.Spec
import FrFlowGen.Old.NoUnauthorizedAccess.Spec
import FrFlowGen.Old.SignedInAreAccepted.Spec
import FrFlowGen.Old.OnlyTheSignedIn.Spec
import FrFlowGen.Old.DisabledHaveNoAccess.Spec
import FrFlowGen.Old.RolesAsGranted.Spec
import FrFlowGen.Old.RealmIsolation.Spec
import FrFlowGen.Old.AnswersNameASession.Spec
import FrFlowGen.Old.SessionsMirrorSignIns.Spec
import FrFlowGen.Old.AccountsAsAdministered.Spec
import FrFlowGen.Old.OneSignInPerToken.Spec
import FrFlowGen.Old.FreshTokens.Spec
import FrFlowGen.Old.HandleRequest.Spec
import FrFlowGen.Old.StoreKeepsState.Spec
import FrFlowGen.Old.Introspect.Spec
import FrFlowGen.Old.SessionLookup.Spec
import FrFlowGen.Old.Domain
import FrFlowGen.Keycloak.realmAccess.Spec
import FrFlowGen.Keycloak.noUnauthorizedAccess.Spec
import FrFlowGen.Keycloak.signedInAreAccepted.Spec
import FrFlowGen.Keycloak.onlyTheSignedIn.Spec
import FrFlowGen.Keycloak.disabledHaveNoAccess.Spec
import FrFlowGen.Keycloak.rolesAsGranted.Spec
import FrFlowGen.Keycloak.accounts.Spec
import FrFlowGen.Keycloak.accountRoles.Spec
import FrFlowGen.Keycloak.signInHistory.Spec
import FrFlowGen.Keycloak.serverRun.Spec
import FrFlowGen.Keycloak.referenceTokens.Spec
import FrFlowGen.Keycloak.realmIsolation.Spec
import FrFlowGen.Keycloak.answersNameASession.Spec
import FrFlowGen.Keycloak.sessionsMirrorSignIns.Spec
import FrFlowGen.Keycloak.accountsAsAdministered.Spec
import FrFlowGen.Keycloak.oneSignInPerToken.Spec
import FrFlowGen.Keycloak.freshTokens.Spec
import FrFlowGen.Keycloak.handleRequest.Spec
import FrFlowGen.Keycloak.storeKeepsState.Spec
import FrFlowGen.Keycloak.introspectAnswers.Spec
import FrFlowGen.Keycloak.sessionLookup.Spec

/-! No statement of keycloak is weakened by the port (ARCHITECTURE section 9, equivalence 4): each node's claim as
today's library stated it (`reference/keycloak`, put in namespace `Old` over the port's types) is equivalent to the
port's. The port states each in every world meeting the store's rules (`Rules`), today's values read in it: the
history and the accounts as loaded are the store's log and its accounts loaded, the state its state, what changes with
the World is read at the world, and a program's or an operation's result is its run's from the world. Today's purpose
was stated over four open types and an acceptance as a pair; the port's acceptance is a record (`Acceptance`), read as
today's pair by `asPair`. Today's definitions of the purpose's words are the port's claims of one equation, each
equivalent to the word being today's define. Today's sessions and accounts were defines over the history replayed by
the step; the port's are those of the state the store holds, which the store's rule `serverRun` says is the history
replayed by the step's code (`next`): under it, each claim about them is today's. Today's definition `serverRun` and
assumption `freshTokens` over the history are the port's rules of the store, `freshTokens` stated pairwise. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Port
open Keycloak

/-- An acceptance as today's pair: the user, and their roles. -/
def asPair (a : Acceptance) : String × List String := (a.user, a.roles)

/-- What an application accepts, as today's: each acceptance a pair. -/
def asPairs (accepted : RealmId → String → Option Acceptance) (r : RealmId) (t : String) :
    Option (String × List String) := (accepted r t).map asPair

theorem pair_some (o : Option Acceptance) (u : String) (rs : List String) :
    o.map asPair = some (u, rs) ↔ o = some (Acceptance.mk u rs) := by
  cases o with
  | none => simp
  | some a => cases a; simp [asPair]

/-- A statement of every acceptance, today's of every pair. -/
theorem forall_pair (o : Option Acceptance) (P : String → List String → Prop) :
    (∀ a, o.map asPair = some a → P a.1 a.2) ↔ (∀ a : Acceptance, o = some a → P a.user a.roles) := by
  cases o with
  | none => simp
  | some b => simp [asPair]

/-- What the store's rules say of a world: what every statement of the port is stated in. -/
def Rules (w : World) : Prop :=
  Keycloak.serverRun w.serverStore ∧ Keycloak.oneSignInPerToken w.serverStore ∧ Keycloak.freshTokens w.serverStore

/-- A statement of every world meeting the rules, its body of the world. -/
theorem in_worlds {P : World → Prop} :
    (∀ w : World, Keycloak.serverRun w.serverStore → Keycloak.oneSignInPerToken w.serverStore →
      Keycloak.freshTokens w.serverStore → P w) ↔ ∀ w, Rules w → P w :=
  ⟨fun h w ⟨h1, h2, h3⟩ => h w h1 h2 h3, fun h w h1 h2 h3 => h w ⟨h1, h2, h3⟩⟩

-- Today's defines of the domain, each the port's.

theorem administer_eq : Old.administer = Keycloak.administer := by
  funext as q; cases q <;> rfl

theorem accountsAfter_eq : Old.accountsAfter = Keycloak.accountsAfter := by
  funext seed hs; unfold Old.accountsAfter Keycloak.accountsAfter; rw [administer_eq]

theorem grantedBy_eq : Old.grantedBy = Keycloak.grantedBy := by
  funext as q; cases q <;> rfl

theorem rolesIn_eq : Old.rolesIn = Keycloak.rolesIn := by
  funext a; cases a <;> rfl

theorem isEnabled_eq : Old.isEnabled = Keycloak.isEnabled := rfl

theorem onlyOne_eq : Old.onlyOne = Keycloak.onlyOne := rfl

theorem endedBy_eq : Old.endedBy = Keycloak.endedBy := by
  funext q x; cases q <;> rfl

theorem opened_eq : Old.opened = Keycloak.opened := by
  funext s q; unfold Old.opened Keycloak.opened; rw [grantedBy_eq]; cases Keycloak.grantedBy s.accounts q <;> rfl

/-- Today's sign-in that still stands, stated as some split of the history; the port's, as no split failing. -/
theorem liveIn_eq : Old.liveIn = Keycloak.liveIn := by
  funext seed hs x
  unfold Old.liveIn Keycloak.liveIn
  rw [grantedBy_eq, accountsAfter_eq]
  apply propext
  simp only [Classical.not_forall, Classical.not_not]
  constructor
  · rintro ⟨pre, post, ⟨q, ha, hb⟩, hc⟩; exact ⟨pre, q, post, ⟨ha, hb⟩, hc⟩
  · rintro ⟨pre, q, post, ⟨ha, hb⟩, hc⟩; exact ⟨pre, post, ⟨q, ha, hb⟩, hc⟩

-- The purpose and its two halves, over today's four types as the port's, in every world meeting the rules.

theorem realmAccess (accepted rolesOf signedIn enabled) :
    Keycloak.realmAccess.claim accepted rolesOf signedIn enabled ↔ ∀ w, Rules w →
      Old.RealmAccess.claim RealmId String String String (asPairs (fun r t => accepted r t w))
        (fun r u => rolesOf r u w) (fun r u t => signedIn r u t w) (fun r u => enabled r u w) := by
  simp only [Keycloak.realmAccess.claim, Old.RealmAccess.claim, asPairs, pair_some]
  exact ⟨fun h w hw r t u => h r t u w hw.1 hw.2.1 hw.2.2, fun h r t u w h1 h2 h3 => h w ⟨h1, h2, h3⟩ r t u⟩

theorem noUnauthorizedAccess (accepted signedIn enabled rolesOf) :
    Keycloak.noUnauthorizedAccess.claim accepted signedIn enabled rolesOf ↔ ∀ w, Rules w →
      Old.NoUnauthorizedAccess.claim RealmId String String String (asPairs (fun r t => accepted r t w))
        (fun r u t => signedIn r u t w) (fun r u => enabled r u w) (fun r u => rolesOf r u w) := by
  simp only [Keycloak.noUnauthorizedAccess.claim, Old.NoUnauthorizedAccess.claim, asPairs]
  exact ⟨fun h w hw r t => (forall_pair (accepted r t w) (fun u rs => (signedIn r u t w ∧ enabled r u w) ∧
      rs = rolesOf r u w)).2 (h r t w hw.1 hw.2.1 hw.2.2),
    fun h r t w h1 h2 h3 => (forall_pair (accepted r t w) (fun u rs => (signedIn r u t w ∧ enabled r u w) ∧
      rs = rolesOf r u w)).1 (h w ⟨h1, h2, h3⟩ r t)⟩

theorem signedInAreAccepted (signedIn enabled accepted rolesOf) :
    Keycloak.signedInAreAccepted.claim signedIn enabled accepted rolesOf ↔ ∀ w, Rules w →
      Old.SignedInAreAccepted.claim RealmId String String String (fun r u t => signedIn r u t w)
        (fun r u => enabled r u w) (asPairs (fun r t => accepted r t w)) (fun r u => rolesOf r u w) := by
  simp only [Keycloak.signedInAreAccepted.claim, Old.SignedInAreAccepted.claim, asPairs, pair_some]
  exact ⟨fun h w hw r t u => h r t u w hw.1 hw.2.1 hw.2.2, fun h r t u w h1 h2 h3 => h w ⟨h1, h2, h3⟩ r t u⟩

theorem onlyTheSignedIn (accepted signedIn) :
    Keycloak.onlyTheSignedIn.claim accepted signedIn ↔ ∀ w, Rules w →
      Old.OnlyTheSignedIn.claim RealmId String String String (asPairs (fun r t => accepted r t w))
        (fun r u t => signedIn r u t w) := by
  simp only [Keycloak.onlyTheSignedIn.claim, Old.OnlyTheSignedIn.claim, asPairs]
  exact ⟨fun h w hw r t => (forall_pair (accepted r t w) (fun u _ => signedIn r u t w)).2 (h r t w hw.1 hw.2.1 hw.2.2),
    fun h r t w h1 h2 h3 => (forall_pair (accepted r t w) (fun u _ => signedIn r u t w)).1 (h w ⟨h1, h2, h3⟩ r t)⟩

theorem disabledHaveNoAccess (accepted enabled) :
    Keycloak.disabledHaveNoAccess.claim accepted enabled ↔ ∀ w, Rules w →
      Old.DisabledHaveNoAccess.claim RealmId String String String (asPairs (fun r t => accepted r t w))
        (fun r u => enabled r u w) := by
  simp only [Keycloak.disabledHaveNoAccess.claim, Old.DisabledHaveNoAccess.claim, asPairs]
  exact ⟨fun h w hw r t => (forall_pair (accepted r t w) (fun u _ => enabled r u w)).2 (h r t w hw.1 hw.2.1 hw.2.2),
    fun h r t w h1 h2 h3 => (forall_pair (accepted r t w) (fun u _ => enabled r u w)).1 (h w ⟨h1, h2, h3⟩ r t)⟩

theorem rolesAsGranted (accepted rolesOf) :
    Keycloak.rolesAsGranted.claim accepted rolesOf ↔ ∀ w, Rules w →
      Old.RolesAsGranted.claim RealmId String String String (asPairs (fun r t => accepted r t w))
        (fun r u => rolesOf r u w) := by
  simp only [Keycloak.rolesAsGranted.claim, Old.RolesAsGranted.claim, asPairs]
  exact ⟨fun h w hw r t => (forall_pair (accepted r t w) (fun u rs => rs = rolesOf r u w)).2
      (h r t w hw.1 hw.2.1 hw.2.2),
    fun h r t w h1 h2 h3 => (forall_pair (accepted r t w) (fun u rs => rs = rolesOf r u w)).1 (h w ⟨h1, h2, h3⟩ r t)⟩

-- Today's definitions, each the port's claim of one equation: the word is today's define, of the world's values.

theorem accounts (enabled) : Keycloak.accounts.claim enabled ↔ ∀ w, Rules w →
    ∀ r u, enabled r u w = Old.enabled w.serverStore.log w.serverStore.loaded r u := by
  unfold Old.enabled; rw [accountsAfter_eq]
  exact ⟨fun h w hw r u => h r u w hw.1 hw.2.1 hw.2.2, fun h r u w h1 h2 h3 => h w ⟨h1, h2, h3⟩ r u⟩

theorem accountRoles (rolesOf) : Keycloak.accountRoles.claim rolesOf ↔ ∀ w, Rules w →
    ∀ r u, rolesOf r u w = Old.rolesOf w.serverStore.log w.serverStore.loaded r u := by
  unfold Old.rolesOf; rw [rolesIn_eq, accountsAfter_eq]
  exact ⟨fun h w hw r u => h r u w hw.1 hw.2.1 hw.2.2, fun h r u w h1 h2 h3 => h w ⟨h1, h2, h3⟩ r u⟩

theorem signInHistory (signedIn) : Keycloak.signInHistory.claim signedIn ↔ ∀ w, Rules w →
    ∀ r u t, signedIn r u t w = Old.signedIn w.serverStore.log w.serverStore.loaded r u t := by
  unfold Old.signedIn; rw [liveIn_eq]
  exact ⟨fun h w hw r u t => h r u t w hw.1 hw.2.1 hw.2.2, fun h r u t w h1 h2 h3 => h w ⟨h1, h2, h3⟩ r u t⟩

theorem referenceTokens (accepted) (introspect : RealmId → String → World → Option Claims × World) :
    Keycloak.referenceTokens.claim introspect accepted ↔ ∀ w, Rules w →
      ∀ r t, asPairs (fun r t => accepted r t w) r t = Old.accepted (fun r t => (introspect r t w).1) r t := by
  have each : ∀ (a : Option Acceptance) (c : Option Claims), a = claimsOf c ↔ a.map asPair = Old.claimsOf c := by
    intro a c
    cases a with
    | none => cases c <;> simp [claimsOf, Old.claimsOf]
    | some a => cases c <;> cases a <;> simp [claimsOf, Old.claimsOf, asPair]
  unfold Keycloak.referenceTokens.claim asPairs Old.accepted
  constructor
  · intro h w hw r t
    have hr := h r t w hw.1 hw.2.1 hw.2.2
    revert hr
    dsimp only
    generalize introspect r t w = p
    rcases p with ⟨res, aft⟩
    exact (each _ _).1
  · intro h r t w h1 h2 h3
    have hr := h w ⟨h1, h2, h3⟩ r t
    revert hr
    dsimp only
    generalize introspect r t w = p
    rcases p with ⟨res, aft⟩
    exact (each _ _).2

-- The store's rules: today's definition of what the server holds, and its assumption of fresh tokens.

/-- What the server holds is the history replayed by the step's code: its sessions and accounts are today's
defines. -/
theorem serverRun (s : Stored) (h : Keycloak.serverRun s) :
    Keycloak.sessions s.state = Old.sessions s.log next s.loaded ∧
      Keycloak.account s.state = Old.account s.log next s.loaded := by
  unfold Keycloak.serverRun at h
  rw [h]
  exact ⟨rfl, rfl⟩

/-- No two sign-ins of the log share a token, pairwise; today's, every sign-in fresh after those before it. -/
theorem freshTokens (s : Stored) : Keycloak.freshTokens s ↔ Old.FreshTokens.claim s.log := by
  unfold Keycloak.freshTokens Old.FreshTokens.claim
  generalize s.log = log
  constructor
  · intro h pre post q hq t ht ⟨p, hp, hpt⟩
    rw [hq, List.pairwise_append] at h
    exact h.2.2 p hp q (List.mem_cons_self) t ht hpt
  · intro h
    induction log with
    | nil => exact List.Pairwise.nil
    | cons a l ih =>
      refine List.Pairwise.cons (fun b hb t ht hat => ?_) (ih fun pre post q hq t ht ⟨p, hp, hpt⟩ =>
        h (a :: pre) post q (by simp [hq]) t ht ⟨p, List.mem_cons_of_mem a hp, hpt⟩)
      obtain ⟨pre, post, hl⟩ := List.append_of_mem hb
      exact h (a :: pre) post b (by simp [hl]) t ht ⟨a, List.mem_cons_self, hat⟩

theorem oneSignInPerToken (s : Stored) : Keycloak.oneSignInPerToken s ↔ Old.OneSignInPerToken.claim s.log s.loaded := by
  unfold Old.OneSignInPerToken.claim; rw [liveIn_eq]; exact Iff.rfl

-- The claims about the sessions and accounts the server holds: today's, of the history replayed, in every world.

theorem sessionsMirrorSignIns : Keycloak.sessionsMirrorSignIns.claim ↔ ∀ w, Rules w →
    Old.SessionsMirrorSignIns.claim (Old.sessions w.serverStore.log next w.serverStore.loaded) w.serverStore.log
      w.serverStore.loaded := by
  unfold Old.SessionsMirrorSignIns.claim; rw [liveIn_eq]
  constructor
  · intro h w hw r x
    rw [← (serverRun _ hw.1).1]
    exact h r x w hw.1 hw.2.1 hw.2.2
  · intro h r x w h1 h2 h3
    have hx := h w ⟨h1, h2, h3⟩ r x
    rw [← (serverRun _ h1).1] at hx
    exact hx

theorem accountsAsAdministered : Keycloak.accountsAsAdministered.claim ↔ ∀ w, Rules w →
    Old.AccountsAsAdministered.claim (Old.account w.serverStore.log next w.serverStore.loaded) w.serverStore.log
      w.serverStore.loaded := by
  unfold Old.AccountsAsAdministered.claim
  constructor
  · intro h w hw r u
    rw [← (serverRun _ hw.1).2]
    exact h r u w hw.1 hw.2.1 hw.2.2
  · intro h r u w h1 h2 h3
    have hx := h w ⟨h1, h2, h3⟩ r u
    rw [← (serverRun _ h1).2] at hx
    exact hx

-- The introspection and the index: today's, of their runs' results from each world.

theorem answersNameASession (introspect : RealmId → String → World → Option Claims × World) :
    Keycloak.answersNameASession.claim introspect ↔ ∀ w, Rules w →
      Old.AnswersNameASession.claim (fun r t => (introspect r t w).1)
        (Old.sessions w.serverStore.log next w.serverStore.loaded) := by
  unfold Old.AnswersNameASession.claim
  constructor
  · intro h w hw r t
    rw [← (serverRun _ hw.1).1]
    have hr := h r t w hw.1 hw.2.1 hw.2.2
    revert hr
    dsimp only
    generalize introspect r t w = p
    rcases p with ⟨res, aft⟩
    exact id
  · intro h r t w h1 h2 h3
    have hr := h w ⟨h1, h2, h3⟩ r t
    rw [← (serverRun _ h1).1] at hr
    revert hr
    dsimp only
    generalize introspect r t w = p
    rcases p with ⟨res, aft⟩
    exact id

theorem introspectAnswers (introspect : RealmId → String → World → Option Claims × World) :
    Keycloak.introspectAnswers.claim introspect ↔ ∀ w, Rules w →
      Old.Introspect.claim (Old.sessions w.serverStore.log next w.serverStore.loaded)
        (Old.account w.serverStore.log next w.serverStore.loaded) (fun r t => (introspect r t w).1) := by
  unfold Old.Introspect.claim Old.Introspect.post; rw [rolesIn_eq, isEnabled_eq, onlyOne_eq]
  constructor
  · intro h w hw r t
    rw [← (serverRun _ hw.1).1, ← (serverRun _ hw.1).2]
    have hr := h r t w hw.1 hw.2.1 hw.2.2
    revert hr
    dsimp only
    generalize introspect r t w = p
    rcases p with ⟨res, aft⟩
    exact id
  · intro h r t w h1 h2 h3
    have hr := h w ⟨h1, h2, h3⟩ r t
    rw [← (serverRun _ h1).1, ← (serverRun _ h1).2] at hr
    revert hr
    dsimp only
    generalize introspect r t w = p
    rcases p with ⟨res, aft⟩
    exact id

theorem sessionLookup (lookup : RealmId → String → StateM Stored (Option Session)) :
    Keycloak.sessionLookup.claim lookup ↔ ∀ w, Rules w →
      Old.SessionLookup.claim (Old.sessions w.serverStore.log next w.serverStore.loaded)
        (fun r t => (ServerStore.lookup_run lookup r t w).1) := by
  unfold Old.SessionLookup.claim Old.SessionLookup.post
  constructor
  · intro h w hw r t
    rw [← (serverRun _ hw.1).1]
    have hr := h r t w hw.1 hw.2.1 hw.2.2
    revert hr
    dsimp only
    generalize ServerStore.lookup_run lookup r t w = p
    rcases p with ⟨res, aft⟩
    exact id
  · intro h r t w h1 h2 h3
    have hr := h w ⟨h1, h2, h3⟩ r t
    rw [← (serverRun _ h1).1] at hr
    revert hr
    dsimp only
    generalize ServerStore.lookup_run lookup r t w = p
    rcases p with ⟨res, aft⟩
    exact id

theorem realmIsolation (introspect : RealmId → String → World → Option Claims × World) :
    Keycloak.realmIsolation.claim introspect ↔ ∀ w, Rules w →
      Old.RealmIsolation.claim (fun r t => (introspect r t w).1) := by
  have each : ∀ (asking : RealmId) (t : String) (res : Option Claims),
      (∀ c, res = some c → c.realm = asking) ↔
        (∀ p ∈ Old.RealmIsolation.view_Introspect asking t res, Old.RealmIsolation.rule p.1 p.2) := by
    intro asking t res
    cases res <;> simp [Old.RealmIsolation.view_Introspect, Old.RealmIsolation.rule]
  unfold Old.RealmIsolation.claim
  constructor
  · intro h w hw r t
    have hr := h r t w hw.1 hw.2.1 hw.2.2
    revert hr
    dsimp only
    generalize introspect r t w = p
    rcases p with ⟨res, aft⟩
    exact (each r t res).1
  · intro h r t w h1 h2 h3
    have hr := h w ⟨h1, h2, h3⟩ r t
    revert hr
    dsimp only
    generalize introspect r t w = p
    rcases p with ⟨res, aft⟩
    exact (each r t res).2

-- One request, and the store: as today stated them, storing a request's run from each world.

theorem handleRequest (step) : Old.HandleRequest.claim step ↔ Keycloak.handleRequest.claim step := by
  unfold Old.HandleRequest.claim Old.HandleRequest.post; rw [administer_eq, endedBy_eq, opened_eq]; exact Iff.rfl

theorem storeKeepsState (record : AuthRequest → ServerState → StateM Stored ServerState) :
    Keycloak.storeKeepsState.claim record ↔ ∀ w : World,
      Old.StoreKeepsState.claim (fun q a => (ServerStore.record_run record q a w).1) := by
  unfold Old.StoreKeepsState.claim Old.StoreKeepsState.post
  constructor
  · intro h w q a
    have hr := h q a w
    revert hr
    dsimp only
    generalize ServerStore.record_run record q a w = p
    rcases p with ⟨res, aft⟩
    exact id
  · intro h q a w
    have hr := h w q a
    revert hr
    dsimp only
    generalize ServerStore.record_run record q a w = p
    rcases p with ⟨res, aft⟩
    exact id

end Port
