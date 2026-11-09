package keycloak

import frflow.*

// ============================================================================
// The server's state: what its requests led to, one at a time
// ============================================================================

val step = Definition[(ServerState, AuthRequest) => ServerState]("the server's handling of one request: the state " +
  "it leads to, from the state before it")

/** The sessions a realm has open, of a state the server holds (`state`, now). */
val sessions = define { (st: Term[ServerState], r: Term[RealmId]) => st.sessions.filter(x => x.realm === r) }

/** The user's account in a realm, of a state the server holds. */
val account = define { (st: Term[ServerState], r: Term[RealmId], u: Term[String]) => accountOf(st.accounts, r, u) }

// ============================================================================
// The server keeps what the history says
// ============================================================================

val sessionsMirrorSignIns = Node.claim("The server holds a session open exactly when its sign-in still stands.")(
  forall((x: Term[Session]) => state.sessions.contains(x) === liveIn(seed, history, x)))
  .refines(onlyTheSignedIn, signedInAreAccepted)

val accountsAsAdministered = Node.claim("The server holds every user's account as loaded at start, with each " +
    "administrator's change applied in turn.")(
  forall((r: Term[RealmId], u: Term[String]) => account(state, r, u) === accountOf(accountsAfter(seed, history), r, u)))
  .refines(disabledHaveNoAccess, rolesAsGranted, signedInAreAccepted)

/** Whether no two sign-ins standing in the history (from the accounts `start`) share a token. */
val oneStandsPerToken = define { (start: Term[List[UserAccount]], hs: Term[List[AuthRequest]]) =>
  forall((x: Term[Session], y: Term[Session]) =>
    (liveIn(start, hs, x) && liveIn(start, hs, y) && x.token === y.token) implies (x === y)) }

val oneSignInPerToken = Node.claim("Two sign-ins that still stand never share a token.")(
  always(serverStore)(s => oneStandsPerToken(s.loaded, s.log)))
  .refines(signedInAreAccepted)
  .assuming(storeOnlyCode, storeOneAtATime, storeStarts)

// ============================================================================
// One request
// ============================================================================

/** Whether an open session holds the session's token. */
val tokenTaken = define { (s: Term[ServerState], x: Term[Session]) => s.sessions.exists(y => y.token === x.token) }

/** The session a request opens: one the accounts grant, under a token no open session holds. */
val opened = define { (s: Term[ServerState], q: Term[AuthRequest]) =>
  grantedBy(s.accounts, q).fold(none[Session])(x => when(tokenTaken(s, x))(none[Session]).otherwise(some(x))) }

/** Whether a request ends the session: a sign-out with its token, in its realm. */
val endedBy = define { (q: Term[AuthRequest], x: Term[Session]) =>
  q.on[AuthRequest.SignOut]((r, t) => x.token === t && x.realm === r)
    .on[AuthRequest.SignIn]((_, _, _, _) => False)
    .on[AuthRequest.SetEnabled]((_, _, _) => False) }

/** Whether the accounts after a request are those before it, with its administrator's change applied. */
val accountsAsAsked = define { (before: Term[ServerState], q: Term[AuthRequest], after: Term[ServerState]) =>
  after.accounts === administer(before.accounts, q) }

/** Whether no session open after a request is one it ends. */
val endedGone = define { (q: Term[AuthRequest], after: Term[ServerState]) =>
  after.sessions.forall(x => !endedBy(q, x)) }

/** Whether every session open before a request, and not ended by it, is open after it. */
val keepsTheRest = define { (before: Term[ServerState], q: Term[AuthRequest], after: Term[ServerState]) =>
  before.sessions.forall(x => endedBy(q, x) || after.sessions.contains(x)) }

/** Whether the session a request opens, if any, is open after it. */
val opensItsOwn = define { (before: Term[ServerState], q: Term[AuthRequest], after: Term[ServerState]) =>
  opened(before, q).forall(x => after.sessions.contains(x)) }

/** Whether every session open after a request was open before it, or is the one it opens. */
val opensNoOther = define { (before: Term[ServerState], q: Term[AuthRequest], after: Term[ServerState]) =>
  after.sessions.forall(x => before.sessions.contains(x) || opened(before, q) === some(x)) }

// Its formula is the five ideas its parts state, one per line.
val handleRequest = Node.claim("A request changes the server's state exactly as it asks.")(
  forall((s: Term[ServerState], q: Term[AuthRequest]) => let(step(s, q))(after =>
    accountsAsAsked(s, q, after) &&
      endedGone(q, after) &&
      keepsTheRest(s, q, after) &&
      opensItsOwn(s, q, after) &&
      opensNoOther(s, q, after))))
  .refines(sessionsMirrorSignIns, accountsAsAdministered)

val requestSetsAccounts = Node.claim("A request changes the accounts only as an administrator's change sets them.")(
  forall((s: Term[ServerState], q: Term[AuthRequest]) => accountsAsAsked(s, q, step(s, q))))
  .refines(handleRequest)

val endedSessionsClose = Node.claim("A request leaves open no session its sign-out ends.")(
  forall((s: Term[ServerState], q: Term[AuthRequest]) => endedGone(q, step(s, q))))
  .refines(handleRequest)

val unendedSessionsStay = Node.claim("A request keeps open every session it does not end.")(
  forall((s: Term[ServerState], q: Term[AuthRequest]) => keepsTheRest(s, q, step(s, q))))
  .refines(handleRequest)

val grantedSessionOpens = Node.claim("A sign-in the accounts grant, under a token no open session holds, opens its " +
    "session.")(
  forall((s: Term[ServerState], q: Term[AuthRequest]) => opensItsOwn(s, q, step(s, q))))
  .refines(handleRequest)

val noOtherSessionOpens = Node.claim("A request opens no session but the one its granted sign-in opens.")(
  forall((s: Term[ServerState], q: Term[AuthRequest]) => opensNoOther(s, q, step(s, q))))
  .refines(handleRequest)

/** The open sessions after a request: the one it opens added, or those it ends removed. */
val sessionsAfter = define { (s: Term[ServerState], q: Term[AuthRequest]) =>
  opened(s, q).fold(s.sessions.filter(y => !endedBy(q, y)))(x => s.sessions :+ x) }

/** The state a request leads to: the accounts as an administrator's change sets them, and the sessions after it. */
val next = define { (s: Term[ServerState], q: Term[AuthRequest]) =>
  make[ServerState](administer(s.accounts, q), sessionsAfter(s, q)) }

/** The state after some requests: from the accounts given and no session, each request handled in turn, as the
  * server's code handles it (`next`, the code of `step`: a rule reads values, not a Definition left open).
  */
val stateAfter = define { (start: Term[List[UserAccount]], hs: Term[List[AuthRequest]]) =>
  hs.foldLeft(make[ServerState](start, Nil: Term[List[Session]]))((s, q) => next(s, q)) }

// What the history is of: the server's own state, and the tokens it is given (rules of the store, kept by its code).
val serverRun = Node.claim("The server's state is what its requests led to, each handled in turn from the " +
    "accounts loaded and no session.")(
  always(serverStore)(s => s.state === stateAfter(s.loaded, s.log)))
  .refines(sessionsMirrorSignIns, accountsAsAdministered)
  .assuming(storeOnlyCode, storeOneAtATime, storeStarts)

/** Whether a later request carries no token an earlier one carried. */
val newToken = define { (earlier: Term[AuthRequest], later: Term[AuthRequest]) =>
  tokenOf(later).forall(t => tokenOf(earlier) =!= some(t)) }

val freshTokens = Node.claim("Every sign-in carries a token no earlier sign-in carried.")(
  always(serverStore)(s => s.log.pairwise(newToken)))
  .refines(oneSignInPerToken, sessionsMirrorSignIns)
  .assuming(storeOnlyCode, storeOneAtATime, storeStarts)

val drawnTokens = Node.assumption("A sign-in the HTTP API hands the server carries a token no handled sign-in " +
    "carried.")(
  forall((handled: Term[List[AuthRequest]]) => fresh(handled, nextRequest(handled).result)))

// ============================================================================
// The server, a program over its store
// ============================================================================

val serve = Definition[Flow[ServerState]]("the server handling the next request it is handed: the state it leads " +
  "to, stored with the request and read back")

/** The next request, drawn against the requests the store has logged, handled on the state the store holds, stored
  * with it; the state read back.
  */
val serving = program {
  for
    h <- logged
    q <- nextRequest(h)
    s <- load
    t <- record(q, next(s, q))
  yield t }
