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
port's. Today's purpose was stated over four open types (`identities` fixed them to realms, strings for tokens, users
and roles) and an acceptance as a pair; the port's acceptance is a record (`Acceptance`), read as today's pair by
`asPair`. Today's definitions of the purpose's words are the port's claims of one equation, each equivalent to the
word being today's define. Today's sessions and accounts were defines over the history replayed; the port's are
those of the state the server holds, which `serverRun` says is the history replayed: under it, each claim about them
is today's. -/

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

-- Today's defines of the domain, each the port's.

theorem administer_eq : Old.administer = Keycloak.administer := by
  funext as q; cases q <;> rfl

theorem accountsAfter_eq : Old.accountsAfter = Keycloak.accountsAfter := by
  funext seed hs; unfold Old.accountsAfter Keycloak.accountsAfter; rw [administer_eq]

theorem grantedBy_eq : Old.grantedBy = Keycloak.grantedBy := by
  funext as q; cases q <;> rfl

theorem rolesIn_eq : Old.rolesIn = Keycloak.rolesIn := by
  funext a; cases a <;> rfl

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

-- The purpose and its two halves, over today's four types as the port's.

theorem realmAccess (accepted rolesOf signedIn enabled) :
    Old.RealmAccess.claim RealmId String String String (asPairs accepted) rolesOf signedIn enabled ↔
      Keycloak.realmAccess.claim accepted rolesOf signedIn enabled := by
  simp only [Old.RealmAccess.claim, Keycloak.realmAccess.claim, asPairs, pair_some]

theorem noUnauthorizedAccess (accepted signedIn enabled rolesOf) :
    Old.NoUnauthorizedAccess.claim RealmId String String String (asPairs accepted) signedIn enabled rolesOf ↔
      Keycloak.noUnauthorizedAccess.claim accepted signedIn enabled rolesOf :=
  ⟨fun h r t => (forall_pair (accepted r t) (fun u rs => (signedIn r u t ∧ enabled r u) ∧ rs = rolesOf r u)).1
      (h r t),
    fun h r t => (forall_pair (accepted r t) (fun u rs => (signedIn r u t ∧ enabled r u) ∧ rs = rolesOf r u)).2
      (h r t)⟩

theorem signedInAreAccepted (signedIn enabled accepted rolesOf) :
    Old.SignedInAreAccepted.claim RealmId String String String signedIn enabled (asPairs accepted) rolesOf ↔
      Keycloak.signedInAreAccepted.claim signedIn enabled accepted rolesOf := by
  simp only [Old.SignedInAreAccepted.claim, Keycloak.signedInAreAccepted.claim, asPairs, pair_some]

theorem onlyTheSignedIn (accepted signedIn) :
    Old.OnlyTheSignedIn.claim RealmId String String String (asPairs accepted) signedIn ↔
      Keycloak.onlyTheSignedIn.claim accepted signedIn :=
  ⟨fun h r t => (forall_pair (accepted r t) (fun u _ => signedIn r u t)).1 (h r t),
    fun h r t => (forall_pair (accepted r t) (fun u _ => signedIn r u t)).2 (h r t)⟩

theorem disabledHaveNoAccess (accepted enabled) :
    Old.DisabledHaveNoAccess.claim RealmId String String String (asPairs accepted) enabled ↔
      Keycloak.disabledHaveNoAccess.claim accepted enabled :=
  ⟨fun h r t => (forall_pair (accepted r t) (fun u _ => enabled r u)).1 (h r t),
    fun h r t => (forall_pair (accepted r t) (fun u _ => enabled r u)).2 (h r t)⟩

theorem rolesAsGranted (accepted rolesOf) :
    Old.RolesAsGranted.claim RealmId String String String (asPairs accepted) rolesOf ↔
      Keycloak.rolesAsGranted.claim accepted rolesOf :=
  ⟨fun h r t => (forall_pair (accepted r t) (fun u rs => rs = rolesOf r u)).1 (h r t),
    fun h r t => (forall_pair (accepted r t) (fun u rs => rs = rolesOf r u)).2 (h r t)⟩

-- Today's definitions, each the port's claim of one equation: the word is today's define.

theorem accounts (enabled history seed) :
    Keycloak.accounts.claim enabled history seed ↔ ∀ r u, enabled r u = Old.enabled history seed r u := Iff.rfl

theorem accountRoles (rolesOf history seed) :
    Keycloak.accountRoles.claim rolesOf history seed ↔ ∀ r u, rolesOf r u = Old.rolesOf history seed r u := by
  unfold Old.rolesOf; rw [rolesIn_eq, accountsAfter_eq]; exact Iff.rfl

theorem signInHistory (signedIn history seed) :
    Keycloak.signInHistory.claim signedIn history seed ↔
      ∀ r u t, signedIn r u t = Old.signedIn history seed r u t := by
  unfold Old.signedIn; rw [liveIn_eq]; exact Iff.rfl

theorem referenceTokens (accepted introspect) :
    Keycloak.referenceTokens.claim accepted introspect ↔
      ∀ r t, asPairs accepted r t = Old.accepted introspect r t := by
  unfold Keycloak.referenceTokens.claim asPairs Old.accepted
  refine forall_congr' fun r => forall_congr' fun t => ?_
  cases accepted r t with
  | none => cases introspect r t <;> simp [claimsOf, Old.claimsOf]
  | some a => cases introspect r t <;> cases a <;> simp [claimsOf, Old.claimsOf, asPair]

/-- What the server holds is the history replayed: its sessions and accounts are today's defines. -/
theorem serverRun (state history seed step) (h : Keycloak.serverRun.claim state history seed step) :
    Keycloak.sessions state = Old.sessions history step seed ∧
      Keycloak.account state = Old.account history step seed := by
  unfold Keycloak.serverRun.claim at h
  subst h
  exact ⟨rfl, rfl⟩

-- The claims about the sessions and accounts the server holds: today's, of the history replayed.

theorem sessionsMirrorSignIns (state history seed step) (h : Keycloak.serverRun.claim state history seed step) :
    Old.SessionsMirrorSignIns.claim (Old.sessions history step seed) history seed ↔
      Keycloak.sessionsMirrorSignIns.claim history state seed := by
  rw [← (serverRun state history seed step h).1]
  unfold Old.SessionsMirrorSignIns.claim; rw [liveIn_eq]; exact Iff.rfl

theorem accountsAsAdministered (state history seed step) (h : Keycloak.serverRun.claim state history seed step) :
    Old.AccountsAsAdministered.claim (Old.account history step seed) history seed ↔
      Keycloak.accountsAsAdministered.claim history state seed := by
  rw [← (serverRun state history seed step h).2]
  exact Iff.rfl

theorem answersNameASession (introspect state history seed step)
    (h : Keycloak.serverRun.claim state history seed step) :
    Old.AnswersNameASession.claim introspect (Old.sessions history step seed) ↔
      Keycloak.answersNameASession.claim introspect state := by
  rw [← (serverRun state history seed step h).1]
  exact Iff.rfl

theorem introspectAnswers (introspect state history seed step)
    (h : Keycloak.serverRun.claim state history seed step) :
    Old.Introspect.claim (Old.sessions history step seed) (Old.account history step seed) introspect ↔
      Keycloak.introspectAnswers.claim introspect state := by
  rw [← (serverRun state history seed step h).1, ← (serverRun state history seed step h).2]
  unfold Old.Introspect.claim Old.Introspect.post; rw [rolesIn_eq]; exact Iff.rfl

theorem sessionLookup (lookup state history seed step) (h : Keycloak.serverRun.claim state history seed step) :
    Old.SessionLookup.claim (Old.sessions history step seed) lookup ↔ Keycloak.sessionLookup.claim lookup state := by
  rw [← (serverRun state history seed step h).1]
  exact Iff.rfl

theorem realmIsolation (introspect) :
    Old.RealmIsolation.claim introspect ↔ Keycloak.realmIsolation.claim introspect := by
  unfold Old.RealmIsolation.claim Keycloak.realmIsolation.claim
  refine forall_congr' fun r => forall_congr' fun t => ?_
  cases introspect r t <;> simp [Old.RealmIsolation.view_Introspect, Old.RealmIsolation.rule]

-- The history, one request, and the store: as today stated them.

theorem oneSignInPerToken (history seed) :
    Old.OneSignInPerToken.claim history seed ↔ Keycloak.oneSignInPerToken.claim history seed := by
  unfold Old.OneSignInPerToken.claim; rw [liveIn_eq]; exact Iff.rfl

theorem freshTokens (history) : Old.FreshTokens.claim history ↔ Keycloak.freshTokens.claim history :=
  ⟨fun h pre q post => h pre post q, fun h pre post q => h pre q post⟩

theorem handleRequest (step) : Old.HandleRequest.claim step ↔ Keycloak.handleRequest.claim step := by
  unfold Old.HandleRequest.claim Old.HandleRequest.post; rw [administer_eq, endedBy_eq, opened_eq]; exact Iff.rfl

theorem storeKeepsState (record) : Old.StoreKeepsState.claim record ↔ Keycloak.storeKeepsState.claim record :=
  Iff.rfl

end Port
