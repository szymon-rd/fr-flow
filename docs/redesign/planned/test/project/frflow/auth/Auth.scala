package auth

import frflow.*

// Auth's purpose as the rebuild writes it (owner §14, §15): `access`, `signedIn` and `authorized` are Declarations,
// abstract ideas known only through the statements about them, never called by code. What refines them ties each to
// the domain, by one equation each, which is also its consistency witness.

final case class UserId(name: String) derives LeanType
final case class Path(value: String) derives LeanType
final case class Grant(user: UserId, path: Path) derives LeanType
final case class Session(token: String, user: UserId) derives LeanType

val access = Declaration[(UserId, Path) => Boolean]("whether the system lets the user reach the path")
val signedIn = Declaration[UserId => Boolean]("whether the user has signed in")
val authorized = Declaration[(UserId, Path) => Boolean](
  "whether the user is allowed the path, by whatever rule the system adopts")

val accessExactly = Node.claim("A user reaches a path exactly when they are signed in and authorized for it.")(
  forall((u: Term[UserId], p: Term[Path]) => access(u, p) === (signedIn(u) && authorized(u, p))))

val grants = Definition[List[Grant]]("the grant table as stored when a request is decided")
val sessions = Definition[List[Session]]("the sessions open when a request is decided")

/** The decision on a request made in a session for a path, given its meaning on the spot: admitted when a grant
  * names the session's user and the path.
  */
val admits = define { (s: Term[Session], p: Term[Path]) => grants.exists(g => g === make[Grant](s.user, p)) }

val grantsAuthorize = Node.claim("A user is authorized for a path exactly when a grant names them and the path.")(
  forall((u: Term[UserId], p: Term[Path]) => authorized(u, p) === grants.exists(g => g === make[Grant](u, p))))
  .refines(accessExactly)

val sessionsSignIn = Node.claim("A user is signed in exactly when a session is open for them.")(
  forall((u: Term[UserId]) => signedIn(u) === sessions.exists(s => s.user === u)))
  .refines(accessExactly)

val requestsReach = Node.claim("A user reaches a path exactly when a request for it is admitted on their behalf.")(
  forall((u: Term[UserId], p: Term[Path]) => access(u, p) === sessions.exists(s => s.user === u && admits(s, p))))
  .refines(accessExactly)

val knowledge = KnowledgeBase("Auth")(accessExactly, grantsAuthorize, sessionsSignIn, requestsReach)
  .implementProvided(grants, sessions)
