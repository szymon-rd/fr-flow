package keycloak

import frflow.*

// ============================================================================
// The domain: realms, accounts, sessions, and the requests the server handles
// ============================================================================

final case class UserAccount(realm: RealmId, username: String, passwordHash: String, enabled: Boolean,
    roles: List[String]) derives LeanType
final case class Session(token: String, realm: RealmId, user: String) derives LeanType

enum AuthRequest derives LeanType:
  /** A sign-in: the password arrives already hashed with the user's salt; `token` is a fresh random value the server
    * drew.
    */
  case SignIn(realm: RealmId, user: String, passwordHash: String, token: String)
  case SignOut(realm: RealmId, token: String)
  /** An administrator enables or disables a user. */
  case SetEnabled(realm: RealmId, user: String, on: Boolean)

// ============================================================================
// Accounts: as loaded, and as administrators set them since
// ============================================================================

/** An administrator's change: enabling or disabling a user of a realm; other requests change no account. */
val administer = define { (as: Term[List[UserAccount]], q: Term[AuthRequest]) =>
  q.on[AuthRequest.SetEnabled]((r, u, on) =>
    as.map(a => when(a.realm === r && a.username === u)(a.updated(_.enabled, on)).otherwise(a)))
    .on[AuthRequest.SignIn]((_, _, _, _) => as)
    .on[AuthRequest.SignOut]((_, _) => as) }

/** The accounts after some requests: as loaded (`start`), with each administrator's change applied in turn. */
val accountsAfter = define { (start: Term[List[UserAccount]], hs: Term[List[AuthRequest]]) =>
  hs.foldLeft(start)((as, q) => administer(as, q)) }

/** The user's account in a realm, if there is one. */
val accountOf = define { (as: Term[List[UserAccount]], r: Term[RealmId], u: Term[String]) =>
  as.find(a => a.realm === r && a.username === u) }

/** Whether there is an account, and it is enabled. */
val isEnabled = define { (a: Term[Option[UserAccount]]) => a.exists(x => x.enabled) }

/** The roles an account has (none without an account). */
val rolesIn = define { (a: Term[Option[UserAccount]]) => a.fold(Nil: Term[List[String]])(x => x.roles) }

val accounts = Node.claim("A user is enabled in a realm exactly when their account there, as loaded and " +
    "administered since, is enabled.")(
  forall((r: Term[RealmId], u: Term[String]) =>
    enabled(r, u) === isEnabled(accountOf(accountsAfter(seed, history), r, u))))
  .refines(disabledHaveNoAccess, signedInAreAccepted)

val accountRoles = Node.claim("A user has the roles their account in the realm gives, as loaded and administered " +
    "since.")(
  forall((r: Term[RealmId], u: Term[String]) =>
    rolesOf(r, u) === rolesIn(accountOf(accountsAfter(seed, history), r, u))))
  .refines(rolesAsGranted, signedInAreAccepted)

// ============================================================================
// Signing in and out, as the history of requests says it
// ============================================================================

/** Whether the user has an enabled account in the realm with that password hash. */
val passwordAccepted = define { (as: Term[List[UserAccount]], r: Term[RealmId], u: Term[String], h: Term[String]) =>
  accountOf(as, r, u).exists(a => a.enabled && a.passwordHash === h) }

/** The session a request asks for, when these accounts grant it: a sign-in by an enabled user with their password. */
val grantedBy = define { (as: Term[List[UserAccount]], q: Term[AuthRequest]) =>
  q.on[AuthRequest.SignIn]((r, u, h, t) =>
    when(passwordAccepted(as, r, u, h))(some(make[Session](t, r, u))).otherwise(none[Session]))
    .on[AuthRequest.SignOut]((_, _) => none[Session])
    .on[AuthRequest.SetEnabled]((_, _, _) => none[Session]) }

/** Whether the history is `pre`, then the request `q`, then `post`. */
val splitsAt = define { (hs: Term[List[AuthRequest]], pre: Term[List[AuthRequest]], q: Term[AuthRequest],
    post: Term[List[AuthRequest]]) => hs === pre ++ (q :: post) }

/** Whether a request coming after `pre` got the session: the accounts then (from `start`) granted it. */
val gotAfter = define { (start: Term[List[UserAccount]], pre: Term[List[AuthRequest]], q: Term[AuthRequest],
    x: Term[Session]) => grantedBy(accountsAfter(start, pre), q) === some(x) }

/** Whether the requests hold a sign-out of the session: one with its token, in its realm. */
val signedOutIn = define { (post: Term[List[AuthRequest]], x: Term[Session]) =>
  post.contains(make[AuthRequest.SignOut](x.realm, x.token)) }

/** Whether a sign-in of the history got the session, with no sign-out of it after. */
val liveIn = define { (start: Term[List[UserAccount]], hs: Term[List[AuthRequest]], x: Term[Session]) =>
  exists((pre: Term[List[AuthRequest]], q: Term[AuthRequest], post: Term[List[AuthRequest]]) =>
    splitsAt(hs, pre, q, post) && gotAfter(start, pre, q, x) && !signedOutIn(post, x)) }

val signInHistory = Node.claim("A user is signed in to a realm with a token exactly when a sign-in of theirs there " +
    "got it and still stands.")(
  forall((r: Term[RealmId], u: Term[String], t: Term[String]) =>
    signedIn(r, u, t) === liveIn(seed, history, make[Session](t, r, u))))
  .refines(onlyTheSignedIn, signedInAreAccepted)

/** The token a sign-in carries. */
val tokenOf = define { (q: Term[AuthRequest]) =>
  q.on[AuthRequest.SignIn]((_, _, _, t) => some(t))
    .on[AuthRequest.SignOut]((_, _) => none[String])
    .on[AuthRequest.SetEnabled]((_, _, _) => none[String]) }

/** Whether a request carries a token no earlier sign-in carried (a request that is no sign-in carries none). */
val fresh = define { (pre: Term[List[AuthRequest]], q: Term[AuthRequest]) =>
  tokenOf(q).forall(t => !pre.exists(p => tokenOf(p) === some(t))) }
