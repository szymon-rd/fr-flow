package frflow.examples.authz

import frflow.dsl.*
import frflow.examples.authz.domain.*

/** Theory of the authorization platform: its domain, the laws of the domain, and
  * the assumptions about the environment.
  */
object AuthzTheory extends Theory("Authz"):

  domain[(UserId, ResourceId, Action, Token, Role, Permission, RbacPolicy, Access)]

  val A1 = assumption(
    id = "A1",
    name = "TokenHolderIsPrincipal",
    statement = "A request presenting a token bound to principal u is issued by u.",
    justification = "Tokens are random, unguessable, sent only over TLS, and never shared or logged."
  )

  val A2 = assumption(
    id = "A2",
    name = "LoginAfterAuthentication",
    statement = "A token is bound to principal u only after u has been authenticated.",
    justification = "Only the authentication service calls login, after verifying the principal's credentials."
  )

  law("EmptyPermitsNothing", "The empty policy permits no access.") {
    (u: UserId, r: ResourceId, a: Action) => !RbacPolicy.empty.permits(u, r, a)
  }

  law("GrantPermits", "A principal that holds a role with a permission is permitted that access.") {
    (p: RbacPolicy, u: UserId, held: Set[Role], role: Role, r: ResourceId, a: Action) =>
      (p.roles.get(u) == Some(held) && held.contains(role) && p.permissions.contains(Permission(role, r, a))) ==>
        p.permits(u, r, a)
  }

  law("RevokeAllDenies", "A principal whose roles are all revoked is permitted nothing.") {
    (p: RbacPolicy, u: UserId, r: ResourceId, a: Action) => !p.revokeAll(u).permits(u, r, a)
  }
