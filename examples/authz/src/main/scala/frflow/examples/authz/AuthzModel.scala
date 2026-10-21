package frflow.examples.authz

import frflow.cli.FrFlowCli
import frflow.dsl.Model
import frflow.examples.authz.domain.*
import frflow.runtime.Service

/** The model: theory, requirements, design, implementation.
  *
  * {{{
  * Theory Authz        domain ADTs, laws, assumptions
  * └── R0  NoUnauthorizedAccess   requirements
  *     └── D1  AuthnThenAuthz     design      [assumes A1, A2]
  *         └── I2  RbacService    implementation (executable)
  * }}}
  */
object AuthzModel extends Model(AuthzTheory, R0, D1, I2)

/** The authorization service: implementation I2, run by FrFlow's runtime.
  *
  * Every call is one step of the machine that was proven to refine D1 and R0, so
  * the audit log satisfies requirement `R0.Safe` (under assumptions A1 and A2).
  */
final class AuthzService:
  private val service = Service(I2)

  def login(user: UserId, token: Token): Boolean = service.submit(I2.login, Login(user, token)).accepted

  def logout(token: Token): Unit = service.submit(I2.logout, Logout(token))

  def access(token: Token, resource: ResourceId, action: Action): Boolean =
    service.submit(I2.access, Request(token, resource, action)).accepted

  /** Publishes a policy and returns its version. */
  def publish(policy: RbacPolicy): Int =
    service.submit(I2.publish, PublishPolicy(policy))
    service.state.version

  def state: ServiceState = service.state

/** `sbt "authz/run <command>"`; `demo` runs the service. `FRFLOW_ROOT=<dir>` points at another workspace. */
@main def authz(args: String*): Unit =
  if args == Seq("demo") then demo()
  else sys.exit(FrFlowCli.run(AuthzModel, FrFlowCli.workspace("examples/authz", "../../../lean"), args))

private def demo(): Unit =
  val svc = AuthzService()
  val alice = UserId("alice")
  val reports = ResourceId("/reports/q3")
  val analyst = Role("analyst")
  val v = svc.publish(RbacPolicy(Map(alice -> Set(analyst)), Set(Permission(analyst, reports, Action.Read))))
  println(s"published policy version $v")
  println(s"login alice: ${svc.login(alice, Token("t-1"))}")
  println(s"alice reads ${reports.path}: ${svc.access(Token("t-1"), reports, Action.Read)}")
  println(s"alice deletes ${reports.path}: ${svc.access(Token("t-1"), reports, Action.Delete)}")
  println(s"unknown token reads ${reports.path}: ${svc.access(Token("forged"), reports, Action.Read)}")
  svc.logout(Token("t-1"))
  println(s"alice reads after logout: ${svc.access(Token("t-1"), reports, Action.Read)}")
  println("audit log:")
  svc.state.log.reverse.foreach(e => println(s"  ${e.user.name} ${e.action} ${e.resource.path} (policy v${e.version})"))
