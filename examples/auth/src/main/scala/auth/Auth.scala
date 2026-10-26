package auth

import frflow.*

// ============================================================================
// The purpose: who can access what
// ============================================================================

val User       = Opaque("User", "a person who uses the system")
val Resource   = Opaque("Resource", "something a user may want to access")
val access     = Param[(User.T, Resource.T) => Boolean]("whether the system lets the user access the resource")
val authorized = Param[(User.T, Resource.T) => Boolean]("whether the user is allowed the resource, by whatever rule the system adopts")
val signedIn   = Param[User.T => Boolean]("whether the user has signed in, so can present who they are")

val accessExactly = Node.claim("A user gets access to a resource exactly when they are signed in and authorized for it.",
  why = "The idea says no one may access what they are not authorized to; and authorization is what lets a signed-in user in, or the system would serve no one. Who is authorized, and how a user signs in, the domain says below."
)(forall((u: Term[User.T], r: Term[Resource.T]) => access(u, r) === (signedIn(u) && authorized(u, r))))

// ============================================================================
// The domain: identities, grants, sessions, and requests
// ============================================================================

final case class UserId(name: String)
final case class Path(value: String)
final case class Grant(user: UserId, path: Path)
object Grant extends Data[Grant]

val grants   = Param[List[Grant]]("the grant table as stored when the request is decided")
val sessions = Param[String => Option[UserId]]("the session table as stored when the request is decided: a token to the user it was issued to at login")
val admit    = Param[(String, Path) => Option[UserId]]("the system's decision on a request (a token and a path): the user it is admitted on behalf of, if any")

val identities = Node.definition("Users are named by ids, and resources are paths.",
  why = "The grant table names users by id and resources by path, so these are what the system knows them by."
)(User := of[UserId], Resource := of[Path])

val grantTable = Node.definition("A user is authorized for a path when a grant names that user and that path.",
  why = "The idea defines authorization as a table of grants; who may change the table is not modelled."
)(authorized := ((u: Term[UserId], p: Term[Path]) => grants.contains(Grant(u, p))))

val sessionTable = Node.definition("A user is signed in when some session token was issued to them.",
  why = "Users identify themselves with tokens they receive at login; the session table records which token was issued to whom. How tokens are issued is not modelled."
)(signedIn := ((u: Term[UserId]) => exists((t: Term[String]) => sessions(t) === Some(u))))

val requests = Node.definition("A user has access to a path when some request for it is admitted on their behalf.",
  why = "A user reaches a resource only through requests, and a request carries a token, not a user: the system sees tokens."
)(access := ((u: Term[UserId], p: Term[Path]) => exists((t: Term[String]) => admit(t, p) === Some(u))))

// ============================================================================
// The parts of the purpose
// ============================================================================

val tokenNamesHolder = Node.claim("A request is admitted only on behalf of the user its token was issued to.",
  why = "A token stands for the user it was issued to: acting for anyone else would let one user in as another."
)(forall((t: Term[String], p: Term[Path]) => admit(t, p).forall(u => sessions(t) === Some(u)))).refines(accessExactly)

val accessNeedsGrant = Node.claim("A request is admitted on behalf of a user only if a grant names that user and the path.",
  why = "No one may access what they are not authorized to, and a grant is what authorizes."
)(forall((t: Term[String], p: Term[Path]) => admit(t, p).forall(u => grants.contains(Grant(u, p))))).refines(accessExactly)

val grantLetsIn = Node.claim("A request whose token was issued to a user with a grant for the path is admitted on their behalf.",
  why = "A grant is there to be used: a system that turned a granted user away would meet the rules by serving no one."
)(forall((t: Term[String], p: Term[Path]) => sessions(t).forall(u => grants.contains(Grant(u, p)) implies (admit(t, p) === Some(u))))).refines(accessExactly)

// ============================================================================
// The contract: what every call of the decision must satisfy
// ============================================================================

val decisionContract = Node.contract(admit)("A request is admitted on behalf of the user its token was issued to, exactly when a grant names that user and the path.",
  why = "The three parts, stated for one call, so every result of the running system can be checked."
)((token, path, decision) => decision.forall(u => sessions(token) === Some(u) && grants.contains(Grant(u, path))) &&
  sessions(token).forall(u => grants.contains(Grant(u, path)) implies (decision === Some(u))))
  .refines(tokenNamesHolder, accessNeedsGrant, grantLetsIn)
  .examples(grants.bind(List(Grant(UserId("alice"), Path("/a")))), sessions.bindTable(Map("t1" -> UserId("alice"))))(
    allows("t1", Path("/a"), Some(UserId("alice")), "Alice's token and a grant for /a: she gets in"),
    allows("t1", Path("/b"), None, "no grant for /b: refused"),
    forbids("t1", Path("/b"), Some(UserId("alice")), "access without a grant is never given"),
    forbids("t2", Path("/a"), Some(UserId("alice")), "a token that is not Alice's never acts for her"),
    forbids("t1", Path("/a"), None, "Alice with a grant for /a is not turned away"))

// ============================================================================
// A design decision: how the service runs
// ============================================================================

val inMemorySessions = Node.design(
  "Sessions and grants are loaded into memory, in one process that decides every request.",
  why = "One service decides access, and the tables fit in memory. A shared store would only be needed with several instances."
)("src/main/scala/auth/Server.scala").refines(decisionContract)

val knowledge = KnowledgeBase("Auth", idea = "IDEA.md")(
  accessExactly,
  identities,
  grantTable,
  sessionTable,
  requests,
  tokenNamesHolder,
  accessNeedsGrant,
  grantLetsIn,
  decisionContract,
  inMemorySessions
).implement(decisionContract)(SessionStore(grants.value.toSet, sessions.value).decide)


object authCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/auth", extensions = List(frflow.agent.Agent))
