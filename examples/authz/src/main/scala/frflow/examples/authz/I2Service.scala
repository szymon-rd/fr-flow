package frflow.examples.authz

import frflow.dsl.*
import frflow.examples.authz.domain.*

/** State of the authorization service.
  * @param version  current policy version
  * @param policies every published policy, by version
  * @param sessions principal bound to each issued token
  * @param log      audit log, most recent first
  */
final case class ServiceState(version: Int, policies: Map[Int, RbacPolicy], sessions: Map[Token, UserId], log: List[Access]):

  /** The principal a token is bound to, or `UserId.Anonymous` for an unknown token. */
  def principal(token: Token): UserId = sessions.getOrElse(token, UserId.Anonymous)

  /** Whether policy version `v` permits `user` to perform `action` on `resource`. */
  def permittedAt(v: Int, user: UserId, resource: ResourceId, action: Action): Boolean =
    policies.get(v).exists(_.permits(user, resource, action))

  /** Whether a request is allowed: its token has a session whose principal the current policy permits. */
  def allows(r: Request): Boolean =
    sessions.get(r.token).exists(u => permittedAt(version, u, r.resource, r.action))

/** An administrator publishes a new RBAC policy version. */
final case class PublishPolicy(policy: RbacPolicy)

/** I2: the implementation. Policies are RBAC data, kept by version for audit. */
object I2
    extends Implementation[ServiceState, SessionState](
      D1,
      id = "I2",
      name = "RbacService",
      statement = "Policies are role-based and versioned, and every decision uses the current version.",
      rationale = "RBAC keeps policies small and reviewable. Published versions are retained, so every audit " +
        "entry can be checked against the policy it was decided under."
    ):

  abstraction(s => SessionState(s.version, v => (u, r, a) => s.permittedAt(v, u, r, a), s.sessions, s.log))

  initial(ServiceState(0, Map.empty, Map.empty, Nil))

  val access = operation[Request]("access", "Decide a request and record it if allowed.")
    .check((s, r) => s.allows(r))
    .act((s, r) => s.copy(log = Access(s.principal(r.token), r.resource, r.action, s.version) :: s.log))
    .refines(D1.access)((_, r) => r)

  val login = operation[Login]("login", "Bind a fresh token to an authenticated principal.")
    .check((s, p) => p.user != UserId.Anonymous && !s.sessions.contains(p.token))
    .act((s, p) => s.copy(sessions = s.sessions.updated(p.token, p.user)))
    .refines(D1.login)((_, p) => p)

  val logout = operation[Logout]("logout", "Revoke a token.")
    .act((s, p) => s.copy(sessions = s.sessions.removed(p.token)))
    .refines(D1.logout)((_, p) => p)

  val publish = operation[PublishPolicy]("publish", "Publish a new policy version and make it current.")
    .act((s, p) => s.copy(version = s.version + 1, policies = s.policies.updated(s.version + 1, p.policy)))
    .refines(D1.setPolicy)((_, p) => SetPolicy((u, r, a) => p.policy.permits(u, r, a)))
