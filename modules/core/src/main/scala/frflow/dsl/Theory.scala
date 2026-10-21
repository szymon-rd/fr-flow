package frflow.dsl

import frflow.lift.{Code, Schema}
import scala.collection.mutable.ListBuffer

/** An environment assumption. Guarantees hold for environments that satisfy it.
  *
  * A layer cites the assumptions its design relies on (`assumes`); an operation
  * can also state one formally as an `assume` clause of its guard, which
  * restricts the environment instead of being enforced by the implementation.
  */
final case class Assumption(id: String, name: String, statement: String, justification: String)

/** A law of the theory: a property of domain functions, stated in Scala and proven in Lean. */
final class Law private[dsl] (val name: String, val statement: String, val code: Code[Any])

/** The theory of a system: its domain, the laws of the domain, and the
  * assumptions about its environment.
  *
  * The domain is a set of Scala ADTs (case classes and enums) and the pure
  * functions defined on them. These are ordinary Scala types, used by the
  * implementation layer as they are; FrFlow translates them to Lean.
  *
  * {{{
  * object AuthzTheory extends Theory("Authz"):
  *   domain[(UserId, ResourceId, Action, RbacPolicy)]
  *   val A1 = assumption("A1", "TokenHolderIsPrincipal", statement = "...", justification = "...")
  *   law("GrantPermits", "A user holding a granted role is permitted.") {
  *     (p: RbacPolicy, u: UserId, role: Role, r: ResourceId, a: Action) => ... ==> p.permits(u, r, a)
  *   }
  * }}}
  */
abstract class Theory(val name: String):
  private val assumptionBuf = ListBuffer.empty[Assumption]
  private val lawBuf = ListBuffer.empty[Law]
  private val domainBuf = ListBuffer.empty[Schema[?]]

  final def assumptions: List[Assumption] = assumptionBuf.toList
  final def laws: List[Law] = lawBuf.toList
  final def domainSchemas: List[Schema[?]] = domainBuf.toList

  /** Declares the domain types of the theory. `T` is one type or a tuple of types. */
  protected final def domain[T](using s: Schema[T]): Unit = domainBuf += s

  protected final def assumption(id: String, name: String, statement: String, justification: String): Assumption =
    val a = Assumption(id, name, statement, justification)
    assumptionBuf += a
    a

  /** States a law. `prop` is a Boolean expression or a lambda returning Boolean;
    * its parameters are universally quantified.
    */
  protected inline def law[F](name: String, statement: String)(inline prop: F): Law =
    registerLaw(name, statement, Code(prop))

  protected final def registerLaw(name: String, statement: String, code: Code[Any]): Law =
    val l = Law(name, statement, code)
    lawBuf += l
    l
