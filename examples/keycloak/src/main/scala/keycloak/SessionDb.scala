package keycloak

import java.util.concurrent.atomic.AtomicReference

/** The server's session store, in memory: the open sessions, and an index by realm and token. The
  * adapter behind the SessionLookup port: what `find` returns is checked against the port on every
  * call (`checkedBy`), and against the define the port is decided with on the port's examples.
  */
final class SessionDb private (initial: List[Session]):
  private val state = AtomicReference(SessionStore(initial))
  @volatile private var index: Map[(RealmId, String), Session] = indexOf(initial)

  private def indexOf(open: List[Session]) = open.map(s => (s.realm, s.token) -> s).toMap

  /** The realm's open session of a token, from the index. */
  def find(realm: RealmId, token: String): Option[Session] = index.get((realm, token))

  /** The open session a token names, in any realm. */
  def byToken(token: String): Option[Session] = state.get.open.find(_.token == token)

  def load(): SessionStore = state.get

  /** Stores `t` in place of what is stored. */
  def save(t: SessionStore): Unit = synchronized {
    state.set(t)
    index = indexOf(t.open)
  }

object SessionDb:
  def of(open: List[Session]): SessionDb = SessionDb(open)
