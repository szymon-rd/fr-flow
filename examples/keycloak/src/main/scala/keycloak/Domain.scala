package keycloak

import frflow.*

// ============================================================================
// The domain: realms, accounts, sessions, and the requests the server handles
// ============================================================================

final case class RealmId(name: String)
final case class UserAccount(realm: RealmId, username: String, passwordHash: String, enabled: Boolean, roles: List[String])
final case class Session(token: String, realm: RealmId, user: String)

enum AuthRequest:
  /** A sign-in: the password arrives already hashed with the user's salt; `token` is a fresh random value the server drew. */
  case SignIn(realm: RealmId, user: String, passwordHash: String, token: String)
  case SignOut(realm: RealmId, token: String)
  /** An administrator enables or disables a user. */
  case SetEnabled(realm: RealmId, user: String, on: Boolean)

val identities = Node.definition("Identities",
  "Realms are named; a user is named by their username in a realm; tokens and roles are strings.",
  why = "The same username in two realms is two users: a user is always looked up with the realm. A token is an opaque random string, a role a name the realm's applications know."
)(Realm := of[RealmId], User := of[String], Token := of[String], Role := of[String])

val seed = Param[List[UserAccount]]("seed", "every realm's accounts as loaded at start: username, salted password hash, whether enabled, realm roles")
val history = Param[List[AuthRequest]]("history",
  "the requests the server has handled since it started, in order: sign-ins, sign-outs and administrators' changes (the server's event log)")

// ============================================================================
// Accounts: as loaded, and as administrators set them since
// ============================================================================

/** An administrator's change: enabling or disabling a user of a realm; other requests change no account. */
val administer = define { (as: List[UserAccount], q: AuthRequest) =>
  q match
    case AuthRequest.SetEnabled(r, u, on) => as.map(a => if a.realm == r && a.username == u then a.copy(enabled = on) else a)
    case AuthRequest.SignIn(_, _, _, _)   => as
    case AuthRequest.SignOut(_, _)        => as
}

/** The accounts after some requests: as loaded, with each administrator's change applied in turn. */
val accountsAfter = define { (hs: List[AuthRequest]) => hs.foldLeft(seed.value)((as, q) => administer(as, q)) }

/** The user's account in a realm, if there is one. */
val accountOf = define { (as: List[UserAccount], r: RealmId, u: String) => as.find(a => a.realm == r && a.username == u) }

/** Whether there is an account, and it is enabled. */
val isEnabled = define { (a: Option[UserAccount]) => a.exists(x => x.enabled) }

/** The roles an account has (none without an account). */
val rolesIn = define { (a: Option[UserAccount]) =>
  a match
    case Some(x) => x.roles
    case None    => Nil
}

val accounts = Node.definition("Accounts",
  "A user is enabled, and has the roles, that their account in the realm says, as loaded at start and as administrators have set it since.",
  why = "Realms and users are loaded at start (managing them is not modelled); an administrator can enable or disable a user, and the next request sees it."
)(enabled := ((r: RealmId, u: String) => isEnabled(accountOf(accountsAfter(history.value), r, u))),
  rolesOf := ((r: RealmId, u: String) => rolesIn(accountOf(accountsAfter(history.value), r, u))))

// ============================================================================
// Signing in and out, as the history of requests says it
// ============================================================================

/** The session a request asks for, when these accounts grant it: a sign-in by an enabled user with their password. */
val grantedBy = define { (as: List[UserAccount], q: AuthRequest) =>
  q match
    case AuthRequest.SignIn(r, u, h, t) => if accountOf(as, r, u).exists(a => a.enabled && a.passwordHash == h) then Some(Session(t, r, u)) else None
    case AuthRequest.SignOut(_, _)       => None
    case AuthRequest.SetEnabled(_, _, _) => None
}

/** Whether a sign-in in the history got the session, granted by the accounts as they were then, and no
  * sign-out with its token in its realm came after it.
  */
val liveIn = define { (hs: List[AuthRequest], x: Session) =>
  exists((pre: List[AuthRequest], post: List[AuthRequest]) =>
    exists((q: AuthRequest) => hs == pre ++ (q :: post) && grantedBy(accountsAfter(pre), q) == Some(x)) &&
      !post.contains(AuthRequest.SignOut(x.realm, x.token)))
}

val signInHistory = Node.definition("SignInHistory",
  "A user is signed in to a realm with a token when a sign-in of theirs to that realm got the token, while they were enabled and with their password, and no sign-out with the token in that realm came after it.",
  why = "This is what signing in and out means, said of the history of requests alone, whatever the server keeps: the server's sessions are proven to follow it (SessionsMirrorSignIns)."
)(signedIn := ((r: RealmId, u: String, t: String) => liveIn(history.value, Session(t, r, u))))

/** The token a sign-in carries. */
val tokenOf = define { (q: AuthRequest) =>
  q match
    case AuthRequest.SignIn(_, _, _, t)  => Some(t)
    case AuthRequest.SignOut(_, _)       => None
    case AuthRequest.SetEnabled(_, _, _) => None
}

/** Whether a request carries a token no earlier sign-in carried (a request that is no sign-in carries none). */
val fresh = define { (pre: List[AuthRequest], q: AuthRequest) =>
  tokenOf(q).forall(t => !pre.exists(p => tokenOf(p) == Some(t)))
}

// ============================================================================
// Accounts the examples use
// ============================================================================

val acme = RealmId("acme")
val globex = RealmId("globex")
val alice = UserAccount(acme, "alice", "h-alice", true, List("admin", "user"))
val bob = UserAccount(acme, "bob", "h-bob", false, List("user"))
val carol = UserAccount(globex, "carol", "h-carol", true, List("viewer"))
val loaded = List(alice, bob)
val bobOn = UserAccount(acme, "bob", "h-bob", true, List("user"))
val atStart = List(alice, bobOn, carol)
/** Alice and Bob sign in to acme, Carol to globex; Bob is disabled; Alice signs in again, and signs out of that session. */
val events = List(
  AuthRequest.SignIn(acme, "alice", "h-alice", "t1"),
  AuthRequest.SignIn(acme, "bob", "h-bob", "t2"),
  AuthRequest.SignIn(globex, "carol", "h-carol", "t4"),
  AuthRequest.SetEnabled(acme, "bob", false),
  AuthRequest.SignIn(acme, "alice", "h-alice", "t3"),
  AuthRequest.SignOut(acme, "t3"))
