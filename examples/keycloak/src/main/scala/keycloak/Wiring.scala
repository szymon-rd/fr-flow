package keycloak

import frflow.*

/** The running server's core: every request goes through `service`, which checks each result against
  * its contract (and the invariants it keeps), and every state change is stored through the store's
  * `storeAfter`, read back and checked against StoreKeepsState. ServiceWiring governs this file.
  */
final class Realms(atStart: List[UserAccount], val db: SessionDb):
  private val handleSide = knowledge.service(handleRequest)(sessionDb.bind(db))
  private val introspectSide = knowledge.service(introspectContract)(
    sessionDb.bind(db), seed.bind(atStart), history.bind(db.events()),
    sessions.bind((r: RealmId) => db.load().sessions.filter(_.realm == r)),
    account.bind((r: RealmId, u: String) => accountOf(db.load().accounts, r, u)))

  /** One sign-in, sign-out or administrator's change, on the stored state, one at a time: the state
    * stored afterwards.
    */
  def handle(q: AuthRequest): ServerState = db.synchronized { handleSide(db.load(), q) }

  /** An administrator enables or disables a user: whether the realm has that user. */
  def setEnabled(realm: RealmId, user: String, on: Boolean): Boolean = db.synchronized {
    val known = db.load().accounts.exists(a => a.realm == realm && a.username == user)
    if known then handle(AuthRequest.SetEnabled(realm, user, on))
    known
  }

  /** What an application of `realm` learns about `token`. */
  def introspect(realm: RealmId, token: String): Option[Claims] = introspectSide(realm, token)
