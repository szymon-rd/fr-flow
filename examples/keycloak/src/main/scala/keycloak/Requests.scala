package keycloak

import frflow.*

// ============================================================================
// The server's state: what its requests led to, one at a time
// ============================================================================

/** What the server keeps: every realm's accounts, and the open sessions. */
final case class ServerState(accounts: List[UserAccount], sessions: List[Session])

val step = Param[(ServerState, AuthRequest) => ServerState]("step",
  "the server's handling of one request: the state it stores, from the state before it")
val sessions = Param[RealmId => List[Session]]("sessions", "the sessions a realm has open, as the server holds them now")
val account = Param[(RealmId, String) => Option[UserAccount]]("account", "the user's account in a realm, as the server holds it now")

/** The state after some requests: from the accounts loaded at start and no session, each request handled in turn. */
val stateAfter = define { (hs: List[AuthRequest]) => hs.foldLeft(ServerState(seed.value, Nil))((s, q) => step(s, q)) }

val serverRun = Node.definition("ServerRun",
  "The server's sessions and accounts now are what its requests led to: from the accounts loaded at start and no session, each request handled in turn.",
  why = "The server handles one request at a time on the state it stored after the last one (ServiceWiring), so its state is the requests of its history applied in turn."
)(sessions := ((r: RealmId) => stateAfter(history.value).sessions.filter(x => x.realm == r)),
  account := ((r: RealmId, u: String) => accountOf(stateAfter(history.value).accounts, r, u)))

// ============================================================================
// The server keeps what the history says
// ============================================================================

val sessionsMirrorSignIns = Node.claim("SessionsMirrorSignIns",
  "The server holds a session open in a realm exactly when its user is signed in to that realm with its token.",
  why = "Applications learn about tokens from the sessions the server holds, so these must be exactly the sign-ins that still stand: one more would let someone in, one less would turn a user away.",
  idea = "Signing in and out"
)(forall((r: RealmId, x: Session) => sessions(r).contains(x) == (x.realm == r && liveIn(history.value, x))))
  .under(onlyTheSignedIn, signedInAreAccepted)

val accountsAsAdministered = Node.claim("AccountsAsAdministered",
  "The server holds every user's account as loaded at start, with each administrator's change applied in turn.",
  why = "Whether a user is enabled is read from the accounts the server holds: they must be the ones administrators set, so disabling a user takes effect at the next request.",
  idea = "Administering users"
)(forall((r: RealmId, u: String) => account(r, u) == accountOf(accountsAfter(history.value), r, u)))
  .under(disabledHaveNoAccess, rolesAsGranted, signedInAreAccepted)

val oneSignInPerToken = Node.claim("OneSignInPerToken",
  "Two sign-ins that still stand never share a token: a token names one session at most.",
  why = "A token must say whose it is: if two users could get the same one, an application could be told either of them."
)(forall((x: Session, y: Session) => (liveIn(history.value, x) && liveIn(history.value, y) && x.token == y.token) ==> (x == y)))
  .under(signedInAreAccepted)

val freshTokens = Node.assumption("FreshTokens",
  "Every sign-in carries a token no earlier sign-in carried.",
  why = "The server draws 256 random bits for each sign-in (HttpApi): a repeat does not happen in practice. Trusted, not proven; the server also refuses a token an open session holds."
)(forall((pre: List[AuthRequest], post: List[AuthRequest]) => forall((q: AuthRequest) =>
  (history.value == pre ++ (q :: post)) ==> fresh(pre, q))))
  .under(oneSignInPerToken, sessionsMirrorSignIns)

// ============================================================================
// Storing the state: the store, outside the proven core
// ============================================================================

val sessionDb = Param[SessionDb]("sessionDb", "the server's store: its accounts, its open sessions indexed by realm and token, and its event log")
val record = Param[(AuthRequest, ServerState) => ServerState]("record",
  "storing a request in the event log, with the state it led to: what the store holds afterwards, read back")

val storeKeepsState = Node.assumption(record)("StoreKeepsState",
  "Storing a request with the state it led to keeps that state: read back, the store holds exactly it.",
  why = "The state lives in a store (in memory here; a database in a cluster). The handling of a request is proven from this promise, not from the store's code; what is stored is read back on every call, so a write the store dropped or changed is seen at once."
)((q, after, back) => back == after)
  .examples(sessionDb.bind(SessionDb.empty))(
    expect(AuthRequest.SignIn(acme, "alice", "h-alice", "t1"), ServerState(loaded, List(Session("t1", acme, "alice"))),
      ServerState(loaded, List(Session("t1", acme, "alice"))), "Alice's new session is stored, and read back"),
    expect(AuthRequest.SignOut(acme, "t1"), ServerState(loaded, Nil), ServerState(loaded, Nil), "after her sign-out, no session is stored"),
    reject(AuthRequest.SignIn(acme, "alice", "h-alice", "t1"), ServerState(loaded, List(Session("t1", acme, "alice"))),
      ServerState(loaded, Nil), "a session the store dropped is seen"))

/** What the store is decided to hold after storing a state: that state. What its code is checked against. */
val storedAs = define { (q: AuthRequest, after: ServerState) => after }

// ============================================================================
// One request
// ============================================================================

/** The session a request opens: one the accounts grant, under a token no open session holds. */
val opened = define { (s: ServerState, q: AuthRequest) =>
  grantedBy(s.accounts, q) match
    case Some(x) => if s.sessions.exists(y => y.token == x.token) then None else Some(x)
    case None    => None
}

/** Whether a request ends the session: a sign-out with its token, in its realm. */
val endedBy = define { (q: AuthRequest, x: Session) =>
  q match
    case AuthRequest.SignOut(r, t)       => x.token == t && x.realm == r
    case AuthRequest.SignIn(_, _, _, _)  => false
    case AuthRequest.SetEnabled(_, _, _) => false
}

val handleRequest = Node.contract(step)("HandleRequest",
  "A request opens the session a sign-in asks for when the user is enabled, the password theirs and no session holds the token; ends the sessions its sign-out names in its realm; changes accounts only as an administrator's change sets them; and changes nothing else.",
  why = "One request at a time, so each result of the running server is checked; the history's meaning (SignInHistory, Accounts) follows by induction over the requests. Refusing a token an open session holds keeps a token naming one session even if a token were ever drawn twice.",
  idea = "Signing in and out"
)((s, q, t) => t.accounts == administer(s.accounts, q) &&
  t.sessions.forall(x => (s.sessions.contains(x) && !endedBy(q, x)) || opened(s, q) == Some(x)) &&
  s.sessions.forall(x => endedBy(q, x) || t.sessions.contains(x)) &&
  opened(s, q).forall(x => t.sessions.contains(x)))
  .under(sessionsMirrorSignIns, accountsAsAdministered)
  .examples(sessionDb.bind(SessionDb.empty))(
    expect(ServerState(loaded, Nil), AuthRequest.SignIn(acme, "alice", "h-alice", "t1"), ServerState(loaded, List(Session("t1", acme, "alice"))),
      "Alice signs in to acme with her password: a session under t1"),
    expect(ServerState(loaded, Nil), AuthRequest.SignIn(acme, "bob", "h-bob", "t2"), ServerState(loaded, Nil),
      "Bob is disabled: no session, even with his password"),
    expect(ServerState(loaded, List(Session("t1", acme, "alice"))), AuthRequest.SignOut(acme, "t1"), ServerState(loaded, Nil),
      "Alice signs out: her session ends"),
    expect(ServerState(loaded, List(Session("t1", acme, "alice"))), AuthRequest.SetEnabled(acme, "alice", false),
      ServerState(List(alice.copy(enabled = false), bob), List(Session("t1", acme, "alice"))), "an administrator disables Alice; her session stays, and is no longer accepted"),
    reject(ServerState(loaded, Nil), AuthRequest.SignIn(acme, "alice", "wrong", "t1"), ServerState(loaded, List(Session("t1", acme, "alice"))),
      "a wrong password never opens a session"),
    reject(ServerState(loaded, Nil), AuthRequest.SignIn(globex, "alice", "h-alice", "t1"), ServerState(loaded, List(Session("t1", globex, "alice"))),
      "Alice is a user of acme, not of globex"),
    reject(ServerState(List(alice, bobOn), List(Session("t1", acme, "alice"))), AuthRequest.SignIn(acme, "bob", "h-bob", "t1"),
      ServerState(List(alice, bobOn), List(Session("t1", acme, "alice"), Session("t1", acme, "bob"))), "a token an open session holds never opens another"),
    reject(ServerState(loaded, List(Session("t1", acme, "alice"))), AuthRequest.SignOut(globex, "t1"), ServerState(loaded, Nil),
      "globex cannot end acme's session"),
    reject(ServerState(loaded, List(Session("t1", acme, "alice"))), AuthRequest.SignOut(acme, "t1"), ServerState(loaded, List(Session("t1", acme, "alice"))),
      "a sign-out is never ignored"),
    reject(ServerState(loaded, Nil), AuthRequest.SignIn(acme, "alice", "h-alice", "t1"), ServerState(loaded, Nil),
      "Alice with her password is not turned away"),
    reject(ServerState(loaded, Nil), AuthRequest.SetEnabled(acme, "bob", true), ServerState(loaded, Nil),
      "an administrator's change is never ignored"))

/** The state a request leads to: the accounts as an administrator's change sets them; the session a
  * sign-in opens added, or the sessions a sign-out ends removed.
  */
val next = define { (s: ServerState, q: AuthRequest) =>
  ServerState(administer(s.accounts, q), opened(s, q) match
    case Some(x) => s.sessions ++ List(x)
    case None    => s.sessions.filter(y => !endedBy(q, y)))
}

/** One request, handled: the state it leads to, stored with the request, as the store reads it back. */
val handle = define { (s: ServerState, q: AuthRequest) => record(q, next(s, q)) }
