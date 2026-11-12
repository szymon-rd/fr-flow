package frflow.dsl.lifted.steps

import frflow.dsl.lifted.{FrSpec, Reader}
import frflow.dsl.service.{ServiceDefinition, ServiceImplementation, ServiceMacros, Services}
import frflow.dsl.vocab.Definition as Defined
import scala.quoted.*

/** `lifted(SpendLimits(BigInt(100), Nil))`: a class that implements a service, read member by member. Its state
  * is the record of its constructor's fields; each member's body is read into a function of that record: what it
  * gives, and, of a member that changes the service, the record after it. A field that is a service is given as
  * that service's Definition (`lifted(StreamProcessor(limits, accounts, checkpoint))`): a call of its member is a
  * call of that Definition's, so the class is proven from the claims on the services it is made with.
  */
object ServiceLift:
  def read[T: Type](service: Expr[T])(using q: Quotes): Expr[ServiceImplementation[T]] =
    val plain = Reader(q)
    import plain.q.reflect.*
    val made = plain.bare(service.asTerm) match
      case Typed(e, _) => plain.bare(e)
      case e           => e
    val (cls, args) = made match
      case Apply(Select(New(tpt), _), args) => (tpt.tpe.typeSymbol, args)
      case other                            => plain.refuse("a service that is not made where it is lifted " +
        "(`lifted(SpendLimits(…))`)", other)
    val trt = plain.serviceOf(TypeRepr.of[T]).filter(_ => plain.isImplementation(cls.typeRef)).getOrElse(
      plain.refuse(s"${cls.name}, which implements no service: a trait that is one of Scala's `caps.Mutable`", made))
    val wiring = plain.stateFields(cls).zip(args).collect {
      case (f, arg) if plain.serviceOf(cls.typeRef.memberType(f)).nonEmpty => f.name -> definition(plain)(arg)
    }.toMap
    '{ val state: FrSpec[T] = ${ ServiceRecord(plain).of[T](cls, trt.name) }
       new ServiceImplementation[T](${ Expr(cls.name) }, state, ${ codes[T](q, cls, Services(Map(trt.fullName ->
         'state), wiring)) }) }

  /** The Definition a service is given as, where the class is made. */
  private def definition(r: Reader)(arg: r.q.reflect.Term)(using Quotes): Expr[Any] =
    import r.q.reflect.*
    val found = new TreeAccumulator[Option[Term]]:
      def foldTree(seen: Option[Term], tree: Tree)(owner: Symbol): Option[Term] = seen.orElse(tree match
        case t: Term if t.tpe <:< TypeRepr.of[ServiceDefinition[?]] => Some(t)
        case other                                                  => foldOverTree(None, other)(owner))
    found.foldTree(None, arg)(Symbol.spliceOwner).fold(r.refuse("a service given to a class FrFlow reads that " +
      "is not a service's Definition (`lifted(StreamProcessor(limits, …))`)", arg))(_.asExpr)

  /** Each member's code, by the member's name. */
  private def codes[T: Type](q: Quotes, cls: Any, services: Services)(using Quotes)
      : Expr[Map[String, Defined[?]]] =
    val code = ServiceCode(StepReader(Reader(q, services), None))
    import code.step.r.q.reflect.*
    val impl = cls.asInstanceOf[Symbol]
    val all = ServiceMacros.members(using code.step.r.q)(TypeRepr.of[T]).map((m, _, result) =>
      '{ (${ Expr(m.name) }, ${ code.of[T](impl, m, result) }) })
    '{ Map[String, Defined[?]](${ Varargs(all) }*) }
