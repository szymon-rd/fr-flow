package frflow.examples.authz.domain

/** A principal: a person or a service that acts on the system.
  * @param name unique login name
  */
final case class UserId(name: String)

object UserId:
  /** The principal of a request whose token is not bound to anyone. */
  val Anonymous: UserId = UserId("")

/** Anything access to which is controlled.
  * @param path location of the resource, for example `/reports/q3`
  */
final case class ResourceId(path: String)

/** An operation a principal can perform on a resource. */
enum Action:
  case Read, Write, Delete

/** A bearer credential issued at login.
  * @param value opaque random string
  */
final case class Token(value: String)

/** A named set of permissions held by principals. */
final case class Role(name: String)

/** Permission for holders of `role` to perform `action` on `resource`. */
final case class Permission(role: Role, resource: ResourceId, action: Action)

/** A role-based access-control policy.
  * @param roles       roles held by each principal
  * @param permissions permissions granted to roles
  */
final case class RbacPolicy(roles: Map[UserId, Set[Role]], permissions: Set[Permission]):

  /** Whether `user` holds a role that is permitted `action` on `resource`. */
  def permits(user: UserId, resource: ResourceId, action: Action): Boolean =
    roles.get(user).exists(held => held.exists(role => permissions.contains(Permission(role, resource, action))))

  /** This policy with every role of `user` revoked. */
  def revokeAll(user: UserId): RbacPolicy = copy(roles = roles.removed(user))

object RbacPolicy:
  /** The policy that permits nothing. */
  val empty: RbacPolicy = RbacPolicy(Map.empty, Set.empty)

/** A recorded access: `user` performed `action` on `resource`, decided under policy version `version`. */
final case class Access(user: UserId, resource: ResourceId, action: Action, version: Int)
