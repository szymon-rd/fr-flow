package keycloak

import examples.Folds.*
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

val seed = Definition[List[UserAccount]]("every realm's accounts as loaded at start: username, salted password " +
  "hash, whether enabled, realm roles")
val history = Definition[List[AuthRequest]]("the requests the server has handled since it started, in order: " +
  "sign-ins, sign-outs and administrators' changes (the server's event log)")

// ============================================================================
// Accounts: as loaded, and as administrators set them since
// ============================================================================

/** An administrator's change: enabling or disabling a user of a realm; other requests change no account. */
val administer = define { (as: Term[List[UserAccount]], q: Term[AuthRequest]) =>
  q.on[AuthRequest.SetEnabled]((r, u, on) =>
    as.mapped(a => when(a.realm === r && a.username === u)(a.updated(_.enabled, on)).otherwise(a)))
    .on[AuthRequest.SignIn]((_, _, _, _) => as)
    .on[AuthRequest.SignOut]((_, _) => as) }

/** The accounts after some requests: as loaded, with each administrator's change applied in turn. */
val accountsAfter = define { (hs: Term[List[AuthRequest]]) =>
  hs.foldLeft(seed: Term[List[UserAccount]])((as, q) => administer(as, q)) }

/** The user's account in a realm, if there is one. */
val accountOf = define { (as: Term[List[UserAccount]], r: Term[RealmId], u: Term[String]) =>
  as.firstWhere(a => a.realm === r && a.username === u) }

/** Whether there is an account, and it is enabled. */
val isEnabled = define { (a: Term[Option[UserAccount]]) => a.someWith(x => x.enabled) }

/** The roles an account has (none without an account). */
val rolesIn = define { (a: Term[Option[UserAccount]]) => a.fold(Nil: Term[List[String]])(x => x.roles) }

val accounts = Node.claim("A user is enabled when their account in the realm says so, as loaded at start and as " +
    "administrators have set it since.")(
  forall((r: Term[RealmId], u: Term[String]) => enabled(r, u) === isEnabled(accountOf(accountsAfter(history), r, u))))
  .refines(realmAccess)

val accountRoles = Node.claim("A user has the roles their account in the realm gives, as loaded at start and as " +
    "administrators have set it since.")(
  forall((r: Term[RealmId], u: Term[String]) => rolesOf(r, u) === rolesIn(accountOf(accountsAfter(history), r, u))))
  .refines(realmAccess)

// ============================================================================
// Signing in and out, as the history of requests says it
// ============================================================================

/** The session a request asks for, when these accounts grant it: a sign-in by an enabled user with their password. */
val grantedBy = define { (as: Term[List[UserAccount]], q: Term[AuthRequest]) =>
  q.on[AuthRequest.SignIn]((r, u, h, t) =>
    when(accountOf(as, r, u).someWith(a => a.enabled && a.passwordHash === h))(some(make[Session](t, r, u)))
      .otherwise(none[Session]))
    .on[AuthRequest.SignOut]((_, _) => none[Session])
    .on[AuthRequest.SetEnabled]((_, _, _) => none[Session]) }

/** Whether a sign-in in the history got the session, granted by the accounts as they were then, and no sign-out with
  * its token in its realm came after it.
  */
val liveIn = define { (hs: Term[List[AuthRequest]], x: Term[Session]) =>
  !forall((pre: Term[List[AuthRequest]], q: Term[AuthRequest], post: Term[List[AuthRequest]]) =>
    !(hs === pre ++ (q :: post) && grantedBy(accountsAfter(pre), q) === some(x) &&
      !post.contains(make[AuthRequest.SignOut](x.realm, x.token)))) }

val signInHistory = Node.claim("A user is signed in to a realm with a token when a sign-in of theirs to that realm " +
    "got the token, while they were enabled and with their password, and no sign-out with the token in that realm " +
    "came after it.")(
  forall((r: Term[RealmId], u: Term[String], t: Term[String]) =>
    signedIn(r, u, t) === liveIn(history, make[Session](t, r, u))))
  .refines(realmAccess)

/** The token a sign-in carries. */
val tokenOf = define { (q: Term[AuthRequest]) =>
  q.on[AuthRequest.SignIn]((_, _, _, t) => some(t))
    .on[AuthRequest.SignOut]((_, _) => none[String])
    .on[AuthRequest.SetEnabled]((_, _, _) => none[String]) }

/** Whether a request carries a token no earlier sign-in carried (a request that is no sign-in carries none). */
val fresh = define { (pre: Term[List[AuthRequest]], q: Term[AuthRequest]) =>
  tokenOf(q).noneOr(t => !pre.exists(p => tokenOf(p) === some(t))) }
