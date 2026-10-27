package keycloak

import examples.Folds.*
import frflow.*

// ============================================================================
// The server's state: what its requests led to, one at a time
// ============================================================================

/** What the server keeps: every realm's accounts, and the open sessions. */
final case class ServerState(accounts: List[UserAccount], sessions: List[Session]) derives LeanType

val step = Definition[(ServerState, AuthRequest) => ServerState]("the server's handling of one request: the state " +
  "it stores, from the state before it")
val state = Definition[ServerState]("the state the server holds now: its accounts and open sessions")

/** The sessions a realm has open, as the server holds them now. */
val sessions = define { (r: Term[RealmId]) => state.sessions.filter(x => x.realm === r) }

/** The user's account in a realm, as the server holds it now. */
val account = define { (r: Term[RealmId], u: Term[String]) => accountOf(state.accounts, r, u) }

/** The state after some requests: from the accounts loaded at start and no session, each request handled in turn. */
val stateAfter = define { (hs: Term[List[AuthRequest]]) =>
  hs.foldLeft(make[ServerState](seed, Nil: Term[List[Session]]))((s, q) => step(s, q)) }

val serverRun = Node.assumption("The server's sessions and accounts now are what its requests led to: from the " +
    "accounts loaded at start and no session, each request handled in turn.")(
  state === stateAfter(history))

// ============================================================================
// The server keeps what the history says
// ============================================================================

val freshTokens = Node.assumption("Every sign-in carries a token no earlier sign-in carried.")(
  forall((pre: Term[List[AuthRequest]], q: Term[AuthRequest], post: Term[List[AuthRequest]]) =>
    (history === pre ++ (q :: post)) implies fresh(pre, q)))

val sessionsMirrorSignIns = Node.claim("The server holds a session open in a realm exactly when its user is signed " +
    "in to that realm with its token.")(
  forall((r: Term[RealmId], x: Term[Session]) => sessions(r).contains(x) === (x.realm === r && liveIn(history, x))))
  .refines(onlyTheSignedIn, signedInAreAccepted)
  .assuming(serverRun, freshTokens)

val accountsAsAdministered = Node.claim("The server holds every user's account as loaded at start, with each " +
    "administrator's change applied in turn.")(
  forall((r: Term[RealmId], u: Term[String]) => account(r, u) === accountOf(accountsAfter(history), r, u)))
  .refines(disabledHaveNoAccess, rolesAsGranted, signedInAreAccepted)
  .assuming(serverRun)

val oneSignInPerToken = Node.claim("Two sign-ins that still stand never share a token: a token names one session " +
    "at most.")(
  forall((x: Term[Session], y: Term[Session]) =>
    (liveIn(history, x) && liveIn(history, y) && x.token === y.token) implies (x === y)))
  .refines(signedInAreAccepted)
  .assuming(freshTokens)

// ============================================================================
// Storing the state: the store, outside the proven core
// ============================================================================

val record = Definition[(AuthRequest, ServerState) => ServerState]("storing a request in the event log, with the " +
  "state it led to: what the store holds afterwards, read back")

val storeKeepsState = Node.assumption("Storing a request with the state it led to keeps that state: read back, the " +
    "store holds exactly it.")(
  forall((q: Term[AuthRequest], after: Term[ServerState]) => record(q, after) === after))

// ============================================================================
// One request
// ============================================================================

/** The session a request opens: one the accounts grant, under a token no open session holds. */
val opened = define { (s: Term[ServerState], q: Term[AuthRequest]) =>
  grantedBy(s.accounts, q).fold(none[Session])(x =>
    when(s.sessions.exists(y => y.token === x.token))(none[Session]).otherwise(some(x))) }

/** Whether a request ends the session: a sign-out with its token, in its realm. */
val endedBy = define { (q: Term[AuthRequest], x: Term[Session]) =>
  q.on[AuthRequest.SignOut]((r, t) => x.token === t && x.realm === r)
    .on[AuthRequest.SignIn]((_, _, _, _) => False)
    .on[AuthRequest.SetEnabled]((_, _, _) => False) }

val handleRequest = Node.claim("A request opens the session a sign-in asks for when the user is enabled, the " +
    "password theirs and no session holds the token; ends the sessions its sign-out names in its realm; changes " +
    "accounts only as an administrator's change sets them; and changes nothing else.")(
  forall((s: Term[ServerState], q: Term[AuthRequest]) => step(s, q).accounts === administer(s.accounts, q) &&
    step(s, q).sessions.forall(x => (s.sessions.contains(x) && !endedBy(q, x)) || opened(s, q) === some(x)) &&
    s.sessions.forall(x => endedBy(q, x) || step(s, q).sessions.contains(x)) &&
    opened(s, q).noneOr(x => step(s, q).sessions.contains(x))))
  .refines(sessionsMirrorSignIns, accountsAsAdministered)

/** The state a request leads to: the accounts as an administrator's change sets them; the session a sign-in opens
  * added, or the sessions a sign-out ends removed.
  */
val next = define { (s: Term[ServerState], q: Term[AuthRequest]) =>
  make[ServerState](administer(s.accounts, q),
    opened(s, q).fold(s.sessions.filter(y => !endedBy(q, y)))(x => s.sessions :+ x)) }

/** One request, handled: the state it leads to, stored with the request, as the store reads it back. */
val handle = define { (s: Term[ServerState], q: Term[AuthRequest]) => record(q, next(s, q)) }
