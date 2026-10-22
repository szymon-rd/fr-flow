package keycloak

import frflow.*

/** The server's store, in memory: the accounts, the open sessions with an index by realm and token, and
  * the event log (the requests handled, in order). The adapter behind SessionLookup: every session `find`
  * returns is checked to be of the realm and token asked, and on the examples it is checked against the
  * define the assumption is decided with. Writes are in SessionWrites.scala.
  */
final class SessionDb private (initial: ServerState):
  private var state = initial
  private var index: Map[(RealmId, String), Session] = indexOf(initial.sessions)
  private var log: Vector[AuthRequest] = Vector.empty

  private def indexOf(open: List[Session]) = open.map(s => (s.realm, s.token) -> s).toMap

  /** The realm's open session of a token, from the index. */
  def find(realm: RealmId, token: String): Option[Session] = synchronized { index.get((realm, token)) }

  /** The state stored now. */
  def load(): ServerState = synchronized { state }

  /** The requests stored so far, in order. */
  def events(): List[AuthRequest] = synchronized { log.toList }

  /** Appends a request to the log, and puts a state in place of the stored one. */
  private[keycloak] def replaceWith(q: AuthRequest, after: ServerState): Unit = synchronized {
    log = log :+ q
    state = after
    index = indexOf(after.sessions)
  }

object SessionDb:
  /** An empty store: no account, no session. */
  def empty: SessionDb = SessionDb(ServerState(Nil, Nil))

  /** A store holding the accounts loaded at start, and no session. */
  def loaded(atStart: List[UserAccount]): SessionDb = SessionDb(ServerState(atStart, Nil))

  /** A store holding what the requests led to from the accounts loaded at start (for the examples). */
  def replaying(atStart: List[UserAccount], requests: List[AuthRequest]): SessionDb =
    val db = loaded(atStart)
    requests.foreach(q => db.replaceWith(q, next(db.load(), q)))
    db
