package frflow.examples.authz

import frflow.dsl.*
import frflow.examples.authz.domain.*

/** A policy as a predicate: whether a principal may perform an action on a resource. */
type Policy = (UserId, ResourceId, Action) => Boolean

/** What the requirement is about: the policy history and the audit log.
  * @param version current policy version
  * @param policy  the policy of every version
  * @param log     accesses that occurred, most recent first
  */
final case class AuditState(version: Int, policy: Int => Policy, log: List[Access])

/** A principal performs an action on a resource. */
final case class AccessAs(user: UserId, resource: ResourceId, action: Action)

/** A new policy version comes into force. */
final case class SetPolicy(policy: Policy)

/** R0: the security goal, independent of any mechanism. */
object R0
    extends Requirements[AuditState](
      AuthzTheory,
      id = "R0",
      name = "NoUnauthorizedAccess",
      statement = "Every recorded access was permitted by the policy in force when it was decided.",
      rationale = "States the security goal without any mechanism. Policies change over time, so the goal is " +
        "relative to the policy version in force at decision time; published versions never change."
    ):

  init(s => s.version == 0 && s.log.isEmpty)

  val access = operation[AccessAs]("access", "A principal performs an action on a resource.")
    .check((s, p) => s.policy(s.version)(p.user, p.resource, p.action))
    .act((s, p) => s.copy(log = Access(p.user, p.resource, p.action, s.version) :: s.log))

  val setPolicy = operation[SetPolicy]("setPolicy", "A new policy version comes into force.")
    .act((s, p) => s.copy(version = s.version + 1, policy = v => if v == s.version + 1 then p.policy else s.policy(v)))

  requirement("Safe", "Every logged access was permitted by the policy version it was decided under, and that version is not in the future.") {
    s => s.log.forall(e => e.version <= s.version && s.policy(e.version)(e.user, e.resource, e.action))
  }
