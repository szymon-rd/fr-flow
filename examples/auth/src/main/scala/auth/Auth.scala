package auth

import frflow.*

// ============================================================================
// Root: the idea, with nothing assumed about users, resources or authorization
// ============================================================================

val User       = Opaque("User", "a person who uses the system")
val Resource   = Opaque("Resource", "something a user may want to access")
val authorized = Param[(User.T, Resource.T) => Boolean]("authorized", "whether the user is allowed the resource, by whatever rule the system adopts")
val signedIn   = Param[User.T => Boolean]("signedIn", "whether the user has signed in, so can present who they are")

/** Model: which users the system allows to access which resources. */
val noUnauthorizedAccess = Node.root[(User.T, Resource.T) => Boolean](
  "NoUnauthorizedAccess",
  "A user is granted access to a resource only if they are authorized, and a signed-in user is granted every resource they are authorized for.",
  why = "The idea says no one may access what they are not authorized to, and that authorization lets a user in. What 'authorized' and 'signed in' mean is left open: the idea fixes them later, as grants and tokens."
)(allows => forall((u: User.T, r: Resource.T) => (allows(u, r) ==> authorized(u, r)) && ((signedIn(u) && authorized(u, r)) ==> allows(u, r))))

// ============================================================================
// Users are known only through tokens (still generic)
// ============================================================================

val Token  = Opaque("Token", "what a user presents with a request, received at login")
val holder = Param[Token.T => Option[User.T]]("holder", "the user a token was issued to, if it is a valid token")

/** Model: the decision on a request, naming the user it grants access to, if any. */
val authenticated = noUnauthorizedAccess.refine[(Token.T, Resource.T) => Option[User.T]](
  "Authenticated",
  "A request is granted on behalf of a user exactly when its token belongs to that user and the user is authorized; a signed-in user holds a token.",
  why = "Users identify themselves with tokens they receive at login, so a decision sees a token, not a user. abs: a user is allowed a resource when some token of theirs is granted it."
)(
  abs  = decide => (u, r) => exists((t: Token.T) => decide(t, r) == Some(u)),
  spec = decide => forall((t: Token.T, r: Resource.T) => decide(t, r).forall(u => holder(t) == Some(u) && authorized(u, r)) &&
    holder(t).forall(u => authorized(u, r) ==> (decide(t, r) == Some(u)))) &&
    forall((u: User.T) => signedIn(u) ==> exists((t: Token.T) => holder(t) == Some(u)))
)

// ============================================================================
// Instantiation: users, resources, tokens and authorization become concrete
// ============================================================================

final case class UserId(name: String)
final case class Path(value: String)
final case class Grant(user: UserId, path: Path)

val grants   = Param[List[Grant]]("grants", "the grant table as stored when the request is decided")
val sessions = Param[String => Option[UserId]]("sessions", "the session table as stored when the request is decided: token to user")

val grantBased = authenticated.instantiate[(String, Path) => Option[UserId]](
  "GrantBased",
  "Users are ids, resources are paths, tokens are strings, and a user is authorized for a path when a grant names both.",
  why = "The idea defines authorization as a table of grants. The token's holder is whatever the session table says; issuing tokens is not modelled."
)(
  User       := of[UserId],
  Resource   := of[Path],
  Token      := of[String],
  authorized := ((u: UserId, p: Path) => grants.value.contains(Grant(u, p))),
  holder     := ((t: String) => sessions(t)),
  signedIn   := ((u: UserId) => exists((t: String) => sessions(t) == Some(u)))
)

// ============================================================================
// Contract: what every call of an implementation must satisfy
// ============================================================================

val decisionContract = grantBased.contract[String, Path, Option[UserId]](
  "DecisionContract",
  "A decision names the user its token belongs to, exactly when a grant covers the path.",
  why = "GrantBased, stated for one call, so every result of the running system can be checked; and a user with a grant gets in, since the idea says a grant lets them."
)((token, path, decision) => decision.forall(u => sessions(token) == Some(u) && grants.value.contains(Grant(u, path))) &&
  sessions(token).forall(u => grants.value.contains(Grant(u, path)) ==> (decision == Some(u))))
  .examples(grants.bind(List(Grant(UserId("alice"), Path("/a")))), sessions.bindTable(Map("t1" -> UserId("alice"))))(
    expect("t1", Path("/a"), Some(UserId("alice")), "Alice's token and a grant for /a: she gets in"),
    expect("t1", Path("/b"), None, "no grant for /b: refused"),
    reject("t1", Path("/b"), Some(UserId("alice")), "access without a grant is never given"),
    reject("t2", Path("/a"), Some(UserId("alice")), "a token that is not Alice's never acts for her"),
    reject("t1", Path("/a"), None, "Alice with a grant for /a is not turned away"))

// ============================================================================
// A design decision: no formal model, but decided and tracked like the rest
// ============================================================================

val inMemorySessions = decisionContract.design(
  "InMemorySessions",
  "Sessions and grants are loaded into memory, in one process that decides every request.",
  why = "One service decides access, and the tables fit in memory. A shared store would only be needed with several instances."
)("src/main/scala/auth/Server.scala")

val knowledge = KnowledgeBase("Auth", idea = "IDEA.md")(
  noUnauthorizedAccess,
  authenticated,
  grantBased,
  decisionContract,
  inMemorySessions
).implement(decisionContract)(SessionStore(grants.value.toSet, sessions.value).decide)


@main def authCli(args: String*): Unit = sys.exit(knowledge.cli(args, root = "examples/auth"))
