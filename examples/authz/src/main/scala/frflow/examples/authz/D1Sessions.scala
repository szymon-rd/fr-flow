package frflow.examples.authz

import frflow.dsl.*
import frflow.examples.authz.domain.*

/** Design state: sessions bind tokens to principals.
  * @param version  current policy version
  * @param policy   the policy of every version
  * @param sessions principal bound to each issued token
  * @param log      accesses that occurred, most recent first
  */
final case class SessionState(version: Int, policy: Int => Policy, sessions: Map[Token, UserId], log: List[Access]):

  /** The principal a token is bound to, or `UserId.Anonymous` for an unknown token. */
  def principal(token: Token): UserId = sessions.getOrElse(token, UserId.Anonymous)

/** A request presenting `token` asks to perform `action` on `resource`. */
final case class Request(token: Token, resource: ResourceId, action: Action)

/** An authenticated principal receives `token`. */
final case class Login(user: UserId, token: Token)

/** `token` is revoked. */
final case class Logout(token: Token)

/** D1: authentication establishes who acts, authorization decides what they may do. */
object D1
    extends Refinement[SessionState, AuditState](
      R0,
      id = "D1",
      name = "AuthnThenAuthz",
      statement = "Access is granted only to the principal bound to the presented token, under the current policy.",
      rationale = "Separates identity (sessions created at login) from permission (the policy decision). The " +
        "system observes only the presented token, so linking it to the real requester relies on A1 and A2."
    ):

  assumes(AuthzTheory.A1, AuthzTheory.A2)

  abstraction(s => AuditState(s.version, s.policy, s.log))

  init(s => s.version == 0 && s.log.isEmpty && s.sessions.isEmpty)

  val access = operation[Request]("access", "A request presenting a token asks to perform an action.")
    .check((s, p) => s.sessions.get(p.token).exists(u => s.policy(s.version)(u, p.resource, p.action)))
    .act((s, p) => s.copy(log = Access(s.principal(p.token), p.resource, p.action, s.version) :: s.log))
    .refines(R0.access)((s, p) => AccessAs(s.principal(p.token), p.resource, p.action))

  val login = operation[Login]("login", "An authenticated principal receives a fresh token.")
    .check((_, p) => p.user != UserId.Anonymous)
    .check((s, p) => !s.sessions.contains(p.token))
    .act((s, p) => s.copy(sessions = s.sessions.updated(p.token, p.user)))
    .refinesSkip

  val logout = operation[Logout]("logout", "A token is revoked.")
    .act((s, p) => s.copy(sessions = s.sessions.removed(p.token)))
    .refinesSkip

  val setPolicy = operation[SetPolicy]("setPolicy", "A new policy version comes into force.")
    .act((s, p) => s.copy(version = s.version + 1, policy = v => if v == s.version + 1 then p.policy else s.policy(v)))
    .refines(R0.setPolicy)((_, p) => p)

  invariant("SessionsNamed", "Every session is bound to a named principal, never to Anonymous.") {
    s => s.sessions.forall((_, u) => u != UserId.Anonymous)
  }
