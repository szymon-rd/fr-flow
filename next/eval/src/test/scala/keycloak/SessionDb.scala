package keycloak

import cats.effect.{IO, Ref}

/** The server's store, in memory: the accounts as loaded, the state with an index of the open sessions by realm and
  * token, and the event log (the requests handled, in order). The plain Scala behind `serverStore`'s operations,
  * tested against what is assumed of `record` and `lookup` on generated runs of the store's operations.
  */
final class SessionDb private (held: Ref[IO, (Stored, Map[(RealmId, String), Session])]):
  /** The state stored now. */
  def load: IO[ServerState] = held.get.map(_._1.state)

  /** Stores a request in the log and the state it led to; returns the state stored afterwards, read back. */
  def record(q: AuthRequest, after: ServerState): IO[ServerState] =
    held.updateAndGet((s, _) => (s.copy(state = after, log = s.log :+ q), SessionDb.indexOf(after))).map(_._1.state)

  /** The realm's open session of a token, from the index. */
  def lookup(realm: RealmId, token: String): IO[Option[Session]] = held.get.map(_._2.get((realm, token)))

  /** What it holds. */
  def stored: IO[Stored] = held.get.map(_._1)

object SessionDb:
  /** A store holding what is given. */
  def holding(s: Stored): IO[SessionDb] = Ref[IO].of((s, indexOf(s.state))).map(SessionDb(_))

  private def indexOf(s: ServerState): Map[(RealmId, String), Session] =
    s.sessions.map(x => (x.realm, x.token) -> x).toMap
