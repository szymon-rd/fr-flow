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
  record.assumed
  lookup.assumed

val nextRequest = Definition[Flow[AuthRequest]]("the next request the HTTP API hands the server: a sign-in, its " +
  "token drawn, a sign-out or an administrator's change")

/** The requests the HTTP API has received and not yet handed the server: known only by what is assumed of the next. */
object inbox extends StateModel[List[AuthRequest]]("the requests the HTTP API has received and not yet handed on"):
  nextRequest.assumed

/** The accounts as loaded at start, the requests handled so far and the state now: the store's, in the World. */
val seed: Term[List[UserAccount]] = serverStore.current.loaded
val history: Term[List[AuthRequest]] = serverStore.current.log
val state: Term[ServerState] = serverStore.current.state

val storeOnlyCode = Node.assumption("Nothing but the server's programs changes what its store holds.")(
  serverStore.onlyCodeChanges)
val storeOneAtATime = Node.assumption("Runs on the store never interleave: the server handles one request at a " +
  "time, and an introspection reads the store between two.")(serverStore.atomic)
val storeStarts = Node.assumption("The store starts with the accounts loaded at start, no session and an empty " +
  "event log.")(serverStore.initially(s => s.state === make[ServerState](s.loaded, Nil: Term[List[Session]]) &&
    s.log === (Nil: Term[List[AuthRequest]])))

val storeKeepsState = Node.assumption("Storing a request with the state it led to keeps that state: read back, the " +
    "store holds exactly it.")(
  forall((q: Term[AuthRequest], after: Term[ServerState]) => record(q, after).result === after))

val storeLogs = Node.assumption("Storing a request with the state it led to holds that state, logs the request at " +
    "the end of the event log, and keeps the accounts as loaded.")(
  forall((q: Term[AuthRequest], after: Term[ServerState]) =>
    serverStore.in(record(q, after).after) === make[Stored](seed, after, history :+ q)))

val handedOneAtATime = Node.assumption("The HTTP API hands the server one request at a time, each once.")(inbox.atomic)

val loadedKept = Node.claim("The accounts as loaded at start never change.")(seed.isConstant)
  .assuming(storeOnlyCode, storeOneAtATime, handedOneAtATime)
