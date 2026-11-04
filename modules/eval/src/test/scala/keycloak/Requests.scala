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

val sessionsMirrorSignIns = Node.claim("The server holds a session open in a realm exactly when its user is signed " +
    "in to that realm with its token.")(
  forall((r: Term[RealmId], x: Term[Session]) =>
    sessions(state, r).contains(x) === (x.realm === r && liveIn(seed, history, x))))
  .refines(onlyTheSignedIn, signedInAreAccepted)

val accountsAsAdministered = Node.claim("The server holds every user's account as loaded at start, with each " +
    "administrator's change applied in turn.")(
  forall((r: Term[RealmId], u: Term[String]) => account(state, r, u) === accountOf(accountsAfter(seed, history), r, u)))
  .refines(disabledHaveNoAccess, rolesAsGranted, signedInAreAccepted)

val oneSignInPerToken = Node.claim("Two sign-ins that still stand never share a token: a token names one session " +
    "at most.")(
  always(serverStore)(s => forall((x: Term[Session], y: Term[Session]) =>
    (liveIn(s.loaded, s.log, x) && liveIn(s.loaded, s.log, y) && x.token === y.token) implies (x === y))))
  .refines(signedInAreAccepted)
  .assuming(storeOnlyCode, storeOneAtATime, storeStarts)

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
    opened(s, q).forall(x => step(s, q).sessions.contains(x))))
  .refines(sessionsMirrorSignIns, accountsAsAdministered)

/** The state a request leads to: the accounts as an administrator's change sets them; the session a sign-in opens
  * added, or the sessions a sign-out ends removed.
  */
val next = define { (s: Term[ServerState], q: Term[AuthRequest]) =>
  make[ServerState](administer(s.accounts, q),
    opened(s, q).fold(s.sessions.filter(y => !endedBy(q, y)))(x => s.sessions :+ x)) }

/** The state after some requests: from the accounts given and no session, each request handled in turn, as the
  * server's code handles it (`next`, the code of `step`: a rule reads values, not a Definition left open).
  */
val stateAfter = define { (start: Term[List[UserAccount]], hs: Term[List[AuthRequest]]) =>
  hs.foldLeft(make[ServerState](start, Nil: Term[List[Session]]))((s, q) => next(s, q)) }

// What the history is of: the server's own state, and the tokens it is given (rules of the store, kept by its code).
val serverRun = Node.claim("The server's sessions and accounts now are what its requests led to: from the " +
    "accounts loaded at start and no session, each request handled in turn.")(
  always(serverStore)(s => s.state === stateAfter(s.loaded, s.log)))
  .refines(sessionsMirrorSignIns, accountsAsAdministered)
  .assuming(storeOnlyCode, storeOneAtATime, storeStarts)

val freshTokens = Node.claim("Every sign-in carries a token no earlier sign-in carried.")(
  always(serverStore)(s => s.log.pairwise((p, q) => tokenOf(q).forall(t => tokenOf(p) =!= some(t)))))
  .refines(oneSignInPerToken, sessionsMirrorSignIns)
  .assuming(storeOnlyCode, storeOneAtATime, storeStarts)

val drawnTokens = Node.assumption("Every sign-in the HTTP API hands the server carries a token it drew, which no " +
    "sign-in among the requests the server has handled, which it is shown, carried.")(
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
