package keycloak

/** The server's store, in memory: the accounts, the open sessions with an index by realm and token, and the event
  * log (the requests handled, in order). The plain Scala behind `record` and `lookup`, tested against
  * `storeKeepsState` and `sessionLookup`.
  */
final class SessionDb private (initial: ServerState):
  private var held = initial
  private var index: Map[(RealmId, String), Session] = indexOf(initial.sessions)
  private var log: Vector[AuthRequest] = Vector.empty

  private def indexOf(open: List[Session]) = open.map(s => (s.realm, s.token) -> s).toMap

  /** The realm's open session of a token, from the index. */
  def find(realm: RealmId, token: String): Option[Session] = synchronized { index.get((realm, token)) }

  /** The state stored now. */
  def load(): ServerState = synchronized { held }

  /** The requests stored so far, in order. */
  def events(): List[AuthRequest] = synchronized { log.toList }

  /** Stores a request in the log and the state it led to; returns the state stored afterwards, read back. */
  def storeAfter(q: AuthRequest, after: ServerState): ServerState = synchronized {
    log = log :+ q
    held = after
    index = indexOf(after.sessions)
    held
  }

object SessionDb:
  /** A store holding a state. */
  def holding(s: ServerState): SessionDb = SessionDb(s)
