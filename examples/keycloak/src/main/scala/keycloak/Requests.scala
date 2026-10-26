package keycloak

import frflow.*

// ============================================================================
// The server's state: what its requests led to, one at a time
// ============================================================================

/** What the server keeps: every realm's accounts, and the open sessions. */
final case class ServerState(accounts: List[UserAccount], sessions: List[Session])
object ServerState extends Data[ServerState]

val step = Param[(ServerState, AuthRequest) => ServerState]("step",
  "the server's handling of one request: the state it stores, from the state before it")
val sessions = Param[RealmId => List[Session]]("sessions", "the sessions a realm has open, as the server holds them now")
val account = Param[(RealmId, String) => Option[UserAccount]]("account", "the user's account in a realm, as the server holds it now")

/** The state after some requests: from the accounts loaded at start and no session, each request handled in turn. */
val stateAfter = define { (hs: Term[List[AuthRequest]]) => hs.foldLeft(ServerState(seed, Nil))((s, q) => step(s, q)) }

val serverRun = Node.definition("ServerRun",
  "The server's sessions and accounts now are what its requests led to: from the accounts loaded at start and no session, each request handled in turn.",
  why = "The server handles one request at a time on the state it stored after the last one (ServiceWiring), so its state is the requests of its history applied in turn."
)(sessions := ((r: Term[RealmId]) => stateAfter(history).sessions.filter(x => x.realm === r)),
  account := ((r: Term[RealmId], u: Term[String]) => accountOf(stateAfter(history).accounts, r, u)))

// ============================================================================
// The server keeps what the history says
// ============================================================================

val sessionsMirrorSignIns = Node.claim("SessionsMirrorSignIns",
  "The server holds a session open in a realm exactly when its user is signed in to that realm with its token.",
  why = "Applications learn about tokens from the sessions the server holds, so these must be exactly the sign-ins that still stand: one more would let someone in, one less would turn a user away.",
  idea = "Signing in and out"
)(forall((r: Term[RealmId], x: Term[Session]) => sessions(r).contains(x) === (x.realm === r && liveIn(history, x))))
  .refines(onlyTheSignedIn, signedInAreAccepted)

val accountsAsAdministered = Node.claim("AccountsAsAdministered",
  "The server holds every user's account as loaded at start, with each administrator's change applied in turn.",
  why = "Whether a user is enabled is read from the accounts the server holds: they must be the ones administrators set, so disabling a user takes effect at the next request.",
  idea = "Administering users"
)(forall((r: Term[RealmId], u: Term[String]) => account(r, u) === accountOf(accountsAfter(history), r, u)))
  .refines(disabledHaveNoAccess, rolesAsGranted, signedInAreAccepted)

val oneSignInPerToken = Node.claim("OneSignInPerToken",
  "Two sign-ins that still stand never share a token: a token names one session at most.",
  why = "A token must say whose it is: if two users could get the same one, an application could be told either of them."
)(forall((x: Term[Session], y: Term[Session]) => (liveIn(history, x) && liveIn(history, y) && x.token === y.token) ==> (x === y)))
  .refines(signedInAreAccepted)

val freshTokens = Node.assumption("FreshTokens",
  "Every sign-in carries a token no earlier sign-in carried.",
  why = "The server draws 256 random bits for each sign-in (HttpApi): a repeat does not happen in practice. Trusted, not proven; the server also refuses a token an open session holds."
)(forall((pre: Term[List[AuthRequest]], post: Term[List[AuthRequest]]) => forall((q: Term[AuthRequest]) =>
  (history === pre ++ (q :: post)) ==> fresh(pre, q))))
  .refines(oneSignInPerToken, sessionsMirrorSignIns)

// ============================================================================
// Storing the state: the store, outside the proven core
// ============================================================================

val sessionDb = Param[SessionDb]("sessionDb", "the server's store: its accounts, its open sessions indexed by realm and token, and its event log")
val record = Param[(AuthRequest, ServerState) => ServerState]("record",
  "storing a request in the event log, with the state it led to: what the store holds afterwards, read back")

val storeKeepsState = Node.assumption(record)("StoreKeepsState",
  "Storing a request with the state it led to keeps that state: read back, the store holds exactly it.",
  why = "The state lives in a store (in memory here; a database in a cluster). The handling of a request is proven from this promise, not from the store's code; what is stored is read back on every call, so a write the store dropped or changed is seen at once."
)((q, after, back) => back === after)
  .examples(sessionDb.bind(SessionDb.empty))(
    expect(AuthRequest.SignIn(acme, "alice", "h-alice", "t1"), ServerState(loaded, List(Session("t1", acme, "alice"))),
      ServerState(loaded, List(Session("t1", acme, "alice"))), "Alice's new session is stored, and read back"),
    expect(AuthRequest.SignOut(acme, "t1"), ServerState(loaded, Nil), ServerState(loaded, Nil), "after her sign-out, no session is stored"),
    never(AuthRequest.SignIn(acme, "alice", "h-alice", "t1"), ServerState(loaded, List(Session("t1", acme, "alice"))),
      ServerState(loaded, Nil), "a session the store dropped is seen"))

/** What the store holds after storing a state: that state. The store's code is checked against it. */
val storedAs = define { (q: Term[AuthRequest], after: Term[ServerState]) => after }

// ============================================================================
// One request
// ============================================================================

/** The session a request opens: one the accounts grant, under a token no open session holds. */
val opened = define { (s: Term[ServerState], q: Term[AuthRequest]) =>
  grantedBy(s.accounts, q)
    .fold(none[Session])(x => s.sessions.exists(y => y.token === x.token).fold(none[Session], some(x)))
}

/** Whether a request ends the session: a sign-out with its token, in its realm. */
val endedBy = define { (q: Term[AuthRequest], x: Term[Session]) =>
  q.on[AuthRequest.SignOut]((r, t) => x.token === t && x.realm === r)
    .on[AuthRequest.SignIn]((_, _, _, _) => False)
    .on[AuthRequest.SetEnabled]((_, _, _) => False)
}

val handleRequest = Node.contract(step)("HandleRequest",
  "A request opens the session a sign-in asks for when the user is enabled, the password theirs and no session holds the token; ends the sessions its sign-out names in its realm; changes accounts only as an administrator's change sets them; and changes nothing else.",
  why = "One request at a time, so each result of the running server is checked; the history's meaning (SignInHistory, Accounts) follows by induction over the requests. Refusing a token an open session holds keeps a token naming one session even if a token were ever drawn twice.",
  idea = "Signing in and out"
)((s, q, t) => t.accounts === administer(s.accounts, q) &&
  t.sessions.forall(x => (s.sessions.contains(x) && !endedBy(q, x)) || opened(s, q) === some(x)) &&
  s.sessions.forall(x => endedBy(q, x) || t.sessions.contains(x)) &&
  opened(s, q).forall(x => t.sessions.contains(x)))
  .refines(sessionsMirrorSignIns, accountsAsAdministered)
  .examples(sessionDb.bind(SessionDb.empty))(
    expect(ServerState(loaded, Nil), AuthRequest.SignIn(acme, "alice", "h-alice", "t1"), ServerState(loaded, List(Session("t1", acme, "alice"))),
      "Alice signs in to acme with her password: a session under t1"),
    expect(ServerState(loaded, Nil), AuthRequest.SignIn(acme, "bob", "h-bob", "t2"), ServerState(loaded, Nil),
      "Bob is disabled: no session, even with his password"),
    expect(ServerState(loaded, List(Session("t1", acme, "alice"))), AuthRequest.SignOut(acme, "t1"), ServerState(loaded, Nil),
      "Alice signs out: her session ends"),
    expect(ServerState(loaded, List(Session("t1", acme, "alice"))), AuthRequest.SetEnabled(acme, "alice", false),
      ServerState(List(alice.copy(enabled = false), bob), List(Session("t1", acme, "alice"))), "an administrator disables Alice; her session stays, and is no longer accepted"),
    never(ServerState(loaded, Nil), AuthRequest.SignIn(acme, "alice", "wrong", "t1"), ServerState(loaded, List(Session("t1", acme, "alice"))),
      "a wrong password never opens a session"),
    never(ServerState(loaded, Nil), AuthRequest.SignIn(globex, "alice", "h-alice", "t1"), ServerState(loaded, List(Session("t1", globex, "alice"))),
      "Alice is a user of acme, not of globex"),
    never(ServerState(List(alice, bobOn), List(Session("t1", acme, "alice"))), AuthRequest.SignIn(acme, "bob", "h-bob", "t1"),
      ServerState(List(alice, bobOn), List(Session("t1", acme, "alice"), Session("t1", acme, "bob"))), "a token an open session holds never opens another"),
    never(ServerState(loaded, List(Session("t1", acme, "alice"))), AuthRequest.SignOut(globex, "t1"), ServerState(loaded, Nil),
      "globex cannot end acme's session"),
    never(ServerState(loaded, List(Session("t1", acme, "alice"))), AuthRequest.SignOut(acme, "t1"), ServerState(loaded, List(Session("t1", acme, "alice"))),
      "a sign-out is never ignored"),
    never(ServerState(loaded, Nil), AuthRequest.SignIn(acme, "alice", "h-alice", "t1"), ServerState(loaded, Nil),
      "Alice with her password is not turned away"),
    never(ServerState(loaded, Nil), AuthRequest.SetEnabled(acme, "bob", true), ServerState(loaded, Nil),
      "an administrator's change is never ignored"))

/** The state a request leads to: the accounts as an administrator's change sets them; the session a
  * sign-in opens added, or the sessions a sign-out ends removed.
  */
val next = define { (s: Term[ServerState], q: Term[AuthRequest]) =>
  ServerState(administer(s.accounts, q), opened(s, q)
    .fold(s.sessions.filter(y => !endedBy(q, y)))(x => s.sessions ++ List(x)))
}

/** One request, handled: the state it leads to, stored with the request, as the store reads it back. */
val handle = define { (s: Term[ServerState], q: Term[AuthRequest]) => record(q, next(s, q)) }
