package keycloak

/** The running server's core: every request goes through `service`, which checks each result
  * against its contract (and the invariants it keeps). ServiceWiring governs this file.
  */
final class Realms(initialAccounts: List[UserAccount], val db: SessionDb):
  private val accounts = java.util.concurrent.atomic.AtomicReference(initialAccounts)
  private val signInOutSide = knowledge.service(signInOut)(users.bind(accounts.get))
  private val introspectSide = knowledge.service(introspectContract)(
    users.bind(accounts.get), sessionsByToken.bind((t: String) => db.byToken(t)), sessionDb.bind(db))

  /** An administrator enables or disables a user (Not modelled: managing users); the next request sees it. */
  def setEnabled(realm: RealmId, user: String, on: Boolean): Boolean =
    val before = accounts.getAndUpdate(_.map(a => if a.realm == realm && a.username == user then a.copy(enabled = on) else a))
    before.exists(a => a.realm == realm && a.username == user)

  /** One sign-in or sign-out: the proven step on the stored sessions, stored back in one go. */
  def handle(q: AuthRequest): SessionStore = db.synchronized {
    val t = signInOutSide(db.load(), q)
    db.save(t)
    t
  }

  /** What an application of `realm` learns about `token`. */
  def introspect(realm: RealmId, token: String): Option[Claims] = introspectSide(realm, token)
