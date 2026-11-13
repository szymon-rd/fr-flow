package auth

import frflow.*

// Auth's nodes in the three kinds (owner §14, §15), each named as today's. `access`, `authorized` and `signedIn` are
// Declarations, known only through the statements about them; today's definition nodes are claims, each an equation
// tying a Declaration to the domain (its consistency witness). `grants` and `sessions` are provided where the code
// runs; `admit` is the plain Scala tested against the claims on it. Today's `exists t` over every token is over the
// tokens of the session table (`admittedTo`). Users are named by ids and resources are paths:
// today's `identities` fixed two open types to these, which the types now say directly.

// ============================================================================
// The purpose: who can access what
// ============================================================================

final case class UserId(name: String) derives RocqType
final case class Path(value: String) derives RocqType

val access = Declaration[(UserId, Path) => Boolean]("whether the system lets the user access the resource")
val authorized = Declaration[(UserId, Path) => Boolean](
  "whether the user is allowed the resource, by whatever rule the system adopts")
val signedIn = Declaration[UserId => Boolean]("whether the user has signed in, so can present who they are")

val accessExactly = Node.claim(
    "A user gets access to a resource exactly when they are signed in and authorized for it.")(
  forall((u: Term[UserId], r: Term[Path]) => access(u, r) === (signedIn(u) && authorized(u, r))))

// ============================================================================
// The domain: identities, grants, sessions, and requests
// ============================================================================

final case class Grant(user: UserId, path: Path) derives RocqType
final case class Session(token: String, user: UserId) derives RocqType

/** The session table: each token with the user it was issued to at login. */
final case class Sessions(open: List[Session]) derives RocqType

val grants = Declaration[List[Grant]]("the grant table as stored when the request is decided")
val sessions = Declaration[Sessions](
  "the session table as stored when the request is decided: a token to the user it was issued to at login")
val admit = Declaration[(String, Path) => Option[UserId]](
  "the system's decision on a request (a token and a path): the user it is admitted on behalf of, if any")

/** A grant names the user and the path. */
val grantFor = define { (u: Term[UserId], p: Term[Path]) => grants.exists(g => g === make[Grant](u, p)) }

/** The user the token was issued to, if any. */
val holderOf = define { (t: Term[String]) => sessions.term.open.find(s => s.token === t).map(s => s.user) }

/** The token's holder has a grant for the path. */
val holderGranted = define { (t: Term[String], p: Term[Path]) => holderOf(t).exists(u => grantFor(u, p)) }

/** Some session's token is admitted for the path on the user's behalf. */
val admittedTo = define { (u: Term[UserId], p: Term[Path]) =>
  sessions.term.open.exists(s => admit(s.token, p) === some(u)) }

val tokensIssuedOnce = Node.assumption("The session table issues each token to one user.")(
  always[Sessions](s => s.open.pairwise((a, b) => a.token =!= b.token)))

val grantTable = Node.claim("A user is authorized for a path exactly when a grant names that user and that path.")(
  forall((u: Term[UserId], p: Term[Path]) => authorized(u, p) === grantFor(u, p)))
  .refines(accessExactly)

val sessionTable = Node.claim("A user is signed in exactly when some session token was issued to them.")(
  forall((u: Term[UserId]) => signedIn(u) === sessions.term.open.exists(s => s.user === u)))
  .refines(accessExactly)

val requests = Node.claim(
    "A user has access to a path exactly when some request for it is admitted on their behalf.")(
  forall((u: Term[UserId], p: Term[Path]) => access(u, p) === admittedTo(u, p)))
  .refines(accessExactly)

// ============================================================================
// The parts of the purpose
// ============================================================================

val tokenNamesHolder = Node.claim("A request is admitted only on behalf of the user its token was issued to.")(
  forall((t: Term[String], p: Term[Path]) => admit(t, p).forall(u => holderOf(t) === some(u))))
  .refines(accessExactly)
  .assuming(tokensIssuedOnce)

val accessNeedsGrant = Node.claim(
    "A request is admitted on behalf of a user only if a grant names that user and the path.")(
  forall((t: Term[String], p: Term[Path]) => admit(t, p).forall(u => grantFor(u, p))))
  .refines(accessExactly)

val grantLetsIn = Node.claim(
    "A request whose token's holder has a grant for the path is admitted on the holder's behalf.")(
  forall((t: Term[String], p: Term[Path]) => holderGranted(t, p) implies (admit(t, p) === holderOf(t))))
  .refines(accessExactly)
  .assuming(tokensIssuedOnce)

// ============================================================================
// What every call of the decision must satisfy
// ============================================================================

val decisionContract = Node.claim(
    "A request is admitted on behalf of its token's holder exactly when they have a grant for the path.")(
  forall((t: Term[String], p: Term[Path]) =>
    admit(t, p) === when(holderGranted(t, p))(holderOf(t)).otherwise(none[UserId])))
  .refines(tokenNamesHolder, accessNeedsGrant, grantLetsIn)
  .assuming(tokensIssuedOnce)

// ============================================================================
// A design decision: how the service runs
// ============================================================================

val inMemorySessions = Node.design(
  "One process decides every request, from the sessions and grants it holds in memory.")(
  "src/main/scala/auth/Server.scala").refines(decisionContract)

val knowledge = FrModel("Auth")(accessExactly, grantTable, sessionTable, requests, tokenNamesHolder,
  accessNeedsGrant, grantLetsIn, decisionContract, inMemorySessions, tokensIssuedOnce,
  // The Definitions of the model's words.
  grants.provided, sessions.provided,
  admit.defineTested(env => SessionStore(env(grants), env(sessions)).decide))
