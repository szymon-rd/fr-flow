package auth

import frflow.*

// ============================================================================
// Root: the idea, with nothing assumed about users, resources or authorization
// ============================================================================

val User       = Opaque("User")
val Resource   = Opaque("Resource")
val authorized = Param[(User.T, Resource.T) => Boolean]("authorized")

/** Model: which users the system allows to access which resources. */
val noUnauthorizedAccess = Node.root[(User.T, Resource.T) => Boolean](
  "NoUnauthorizedAccess",
  "A user is never granted access to a resource they are not authorized to access."
)(allows => forall((u: User.T, r: Resource.T) => allows(u, r) ==> authorized(u, r)))

// ============================================================================
// Users are known only through tokens (still generic)
// ============================================================================

val Token  = Opaque("Token")
val holder = Param[Token.T => Option[User.T]]("holder")

/** Model: the decision on a request, naming the user it grants access to, if any. */
val authenticated = noUnauthorizedAccess.refine[(Token.T, Resource.T) => Option[User.T]](
  "Authenticated",
  "A request is granted on behalf of a user only if its token belongs to that user and the user is authorized."
)(
  abs  = decide => (u, r) => exists((t: Token.T) => decide(t, r) == Some(u)),
  spec = decide => forall((t: Token.T, r: Resource.T) => decide(t, r).forall(u => holder(t) == Some(u) && authorized(u, r)))
)

// ============================================================================
// Instantiation: users, resources, tokens and authorization become concrete
// ============================================================================

final case class UserId(name: String)
final case class Path(value: String)
final case class Grant(user: UserId, path: Path)

val grants   = Param[List[Grant]]("grants")
val sessions = Param[String => Option[UserId]]("sessions")

val grantBased = authenticated.instantiate[(String, Path) => Option[UserId]](
  "GrantBased",
  "Users are ids, resources are paths, tokens are strings, and a user is authorized for a path when a grant names both."
)(
  User       := of[UserId],
  Resource   := of[Path],
  Token      := of[String],
  authorized := ((u: UserId, p: Path) => grants.value.contains(Grant(u, p))),
  holder     := ((t: String) => sessions(t))
)

// ============================================================================
// Contract: what every call of an implementation must satisfy
// ============================================================================

val decisionContract = grantBased.contract[String, Path, Option[UserId]](
  "DecisionContract",
  "A decision names the user its token belongs to, and only when a grant covers the path."
)((token, path, decision) => decision.forall(u => sessions(token) == Some(u) && grants.value.contains(Grant(u, path))))

val knowledge = KnowledgeBase("Auth", idea = "IDEA.md")(
  noUnauthorizedAccess,
  authenticated,
  grantBased,
  decisionContract
)

// ============================================================================
// Implementation: plain Scala, attached to the contract
// ============================================================================

/** Any code and any data structures. */
final class SessionStore(grantTable: Set[Grant], tokens: Map[String, UserId]):
  def decide(token: String, path: Path): Option[UserId] =
    tokens.get(token).filter(u => grantTable.contains(Grant(u, path)))

/** The running decision: the implementation, with every result checked against the contract. */
def service(grantTable: List[Grant], tokens: Map[String, UserId]): (String, Path) => Option[UserId] =
  decisionContract.enforce(SessionStore(grantTable.toSet, tokens).decide)(
    grants.bind(grantTable),
    sessions.bind(t => tokens.get(t))
  )

@main def authCli(args: String*): Unit = sys.exit(knowledge.cli(args, root = "examples/auth"))
