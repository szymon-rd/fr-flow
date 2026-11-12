package frflow.dsl.lifted.steps

import frflow.dsl.lifted.{FrSpec, Reader}
import frflow.dsl.service.{ServiceDefinition, ServiceMacros, Services}
import frflow.dsl.term.Lift
import frflow.dsl.term.Term as DTerm
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
    val (cls, args) = made(plain)(service.asTerm)
    val trt = implemented(plain)(cls, service.asTerm)
    val wiring = plain.stateFields(cls).zip(args).collect {
      case (f, arg) if plain.serviceOf(cls.typeRef.memberType(f)).nonEmpty => f.name -> definition(plain)(arg)
    }.toMap
    '{ val state: FrSpec[T] = ${ ServiceRecord(plain).of[T](cls, trt.name) }
       new ServiceImplementation[T](${ Expr(cls.name) }, state, ${ codes[T](q, cls, Services(Map(trt.fullName ->
         'state), wiring)) }) }

  /** `limits.holding(SpendLimits(BigInt(100), Nil))`: an object of a class that implements a service, as a state
    * of the service: the record of its constructor's fields, a service it is made with the record of the object
    * given for it.
    */
  def held[T: Type, S: Type](service: Expr[T])(using q: Quotes): Expr[DTerm[S]] =
    import q.reflect.*
    '{ val state = ${ stateOf(q, service.asTerm) }.asInstanceOf[FrSpec[Any]]
       Lift.constant[Any](ServiceType.held(state, $service))(using state)
         .asInstanceOf[DTerm[S]] } // a state is typed by the service's name

  private def stateOf(q: Quotes, at: Any)(using Quotes): Expr[FrSpec[?]] =
    val plain = Reader(q)
    import plain.q.reflect.*
    val (cls, args) = made(plain)(at.asInstanceOf[Term])
    val trt = implemented(plain)(cls, at.asInstanceOf[Term])
    val held = plain.stateFields(cls).zip(args).flatMap((f, arg) =>
      plain.serviceOf(cls.typeRef.memberType(f)).map(s => s.fullName -> stateOf(q, arg))).toMap
    trt.typeRef.asType match
      case '[t] => ServiceRecord(Reader(q, Services(held, Map.empty))).of[t](cls, trt.name)

  /** The class an object is made of where it is given, and what its constructor is given. */
  private def made(r: Reader)(service: r.q.reflect.Term): (r.q.reflect.Symbol, List[r.q.reflect.Term]) =
    import r.q.reflect.*
    r.bare(service) match
      case Apply(Select(New(tpt), _), args) => (tpt.tpe.typeSymbol, args)
      case other                            => r.refuse("a service that is not made where it is given " +
        "(`lifted(SpendLimits(…))`)", other)

  /** The service a class implements. */
  private def implemented(r: Reader)(cls: r.q.reflect.Symbol, at: r.q.reflect.Term): r.q.reflect.Symbol =
    r.serviceOf(cls.typeRef).filter(_ => r.isImplementation(cls.typeRef)).getOrElse(r.refuse(
      s"${cls.name}, which implements no service: a trait that is one of Scala's `caps.Mutable`", at))

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
    val all = ServiceMacros.members(using code.step.r.q)(TypeRepr.of[T]).flatMap((m, _, result) =>
      '{ (${ Expr(m.name) }, ${ code.of[T](impl, m, result) }) } :: code.among[T](impl, m, result).toList.map(c =>
        '{ (${ Expr(ServiceImplementation.among(m.name)) }, $c) }))
    '{ Map[String, Defined[?]](${ Varargs(all) }*) }
