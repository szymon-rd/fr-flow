package keycloak

import frflow.*

// ============================================================================
// The server's store, and the requests it is handed: the World's (owner §45 D)
// ============================================================================

/** What the server keeps: every realm's accounts, and the open sessions. */
final case class ServerState(accounts: List[UserAccount], sessions: List[Session]) derives LeanType

/** What the server's store holds: every realm's accounts as loaded at start, the state now, and the event log (the
  * requests handled since it started, in order).
  */
final case class Stored(loaded: List[UserAccount], state: ServerState, log: List[AuthRequest]) derives LeanType

val load = Definition[Flow[ServerState]]("the state the store holds now: its accounts and open sessions")
val logged = Definition[Flow[List[AuthRequest]]]("the event log the store holds now: the requests handled since it " +
  "started, in order")
val record = Definition[(AuthRequest, ServerState) => Flow[ServerState]]("storing a request in the event log, with " +
  "the state it led to: what the store holds afterwards, read back")
val lookup = Definition[(RealmId, String) => Flow[Option[Session]]]("the store's answer to looking up a token's " +
  "session in a realm, from its index by realm and token")

/** The server's store as the proofs see it: what it holds now is read; storing a request and looking a token up are
  * known only by what is assumed of them (G2).
  */
object serverStore extends StateModel[Stored]("the server's store: every realm's accounts as loaded at start, the " +
    "server's state now, and the event log"):
  load.means(state.get.map(s => s.state))
  logged.means(state.get.map(s => s.log))
  record.assumed
  lookup.assumed

val nextRequest = Definition[List[AuthRequest] => Flow[AuthRequest]]("the next request the HTTP API hands the " +
  "server, shown the requests the server has handled: a sign-in, its token drawn, a sign-out or an administrator's " +
  "change")

/** The requests the HTTP API has received and not yet handed the server: known only by what is assumed of the next. */
object inbox extends StateModel[List[AuthRequest]]("the requests the HTTP API has received and not yet handed on"):
  nextRequest.assumed

/** The accounts as loaded at start, the requests handled so far and the state now: the store's, in the World. */
val seed: Term[List[UserAccount]] = serverStore.current.loaded
val history: Term[List[AuthRequest]] = serverStore.current.log
val state: Term[ServerState] = serverStore.current.state

val storeOnlyCode = Node.assumption("Nothing but the server's programs changes what its store holds.")(
  serverStore.onlyCodeChanges)
// The server handles one request at a time, and an introspection reads the store between two.
val storeOneAtATime = Node.assumption("Runs on the store never interleave.")(serverStore.atomic)

/** The store as loaded, before any request: the accounts given, no session, an empty event log. */
val freshStore = define { (as: Term[List[UserAccount]]) =>
  make[Stored](as, make[ServerState](as, Nil: Term[List[Session]]), Nil: Term[List[AuthRequest]]) }

val storeStarts = Node.assumption("The store starts as loaded, before any request.")(
  serverStore.initially(s => s === freshStore(s.loaded)))

val storeKeepsState = Node.assumption("Storing a request with a state reads that state back.")(
  forall((q: Term[AuthRequest], after: Term[ServerState]) => record(q, after).result === after))

val storeHoldsState = Node.assumption("Storing a request with a state leaves the store holding that state.")(
  forall((q: Term[AuthRequest], after: Term[ServerState]) => serverStore.in(record(q, after).after).state === after))

val storeAppendsLog = Node.assumption("Storing a request logs it at the end of the event log.")(
  forall((q: Term[AuthRequest], after: Term[ServerState]) =>
    serverStore.in(record(q, after).after).log === history :+ q))

val storeKeepsLoaded = Node.assumption("Storing a request keeps the accounts as loaded.")(
  forall((q: Term[AuthRequest], after: Term[ServerState]) => serverStore.in(record(q, after).after).loaded === seed))

val handedOneAtATime = Node.assumption("The HTTP API hands the server one request at a time.")(inbox.atomic)

val loadedKept = Node.claim("The accounts as loaded at start never change.")(seed.isConstant)
  .assuming(storeOnlyCode, storeOneAtATime, handedOneAtATime)
