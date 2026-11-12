package frflow.dsl.lifted.steps

import frflow.dsl.lifted.{FrSpec, Reader}
import frflow.dsl.service.{ServiceDeclaration, ServiceMacros, Services}
import frflow.dsl.term.Lift
import frflow.dsl.term.Term as DTerm
import frflow.dsl.vocab.Definition as Defined
import scala.quoted.*

/** `lifted[SpendLimits]`: a class that implements a service, read member by member. Its state is the record of
  * its constructor's fields; each member's body is read into a function of that record: what it gives, and, of a
  * member that changes the service, the record after it. A class that holds services is given the word of each,
  * in the order its constructor takes them (`lifted[StreamProcessor](limits, accounts, checkpoint)`): a call of a
  * held service's member is a call of that word's, so the class is proven from the claims on the services it is
  * made with.
  */
object ServiceLift:
  def read[C: Type](words: Expr[Seq[ServiceDeclaration[?]]])(using q: Quotes): Expr[ServiceImplementation[C]] =
    words match
      case Varargs(given_) => of[C](given_.toList)
      case _               => q.reflect.report.errorAndAbort("FrFlow: lifted is given the words of the services " +
        "a class holds one by one")

  /** A class that holds no service. */
  def alone[C: Type](using Quotes): Expr[ServiceImplementation[C]] = of[C](Nil)

  /** The class `C` read, each service it holds the word given for it. */
  private def of[C: Type](words: List[Expr[ServiceDeclaration[?]]])(using q: Quotes): Expr[ServiceImplementation[C]] =
    val plain = Reader(q)
    import plain.q.reflect.*
    val cls = TypeRepr.of[C].typeSymbol
    implemented(plain)(cls).typeRef.asType match
      case '[t] => '{ ${ typed[t](q, cls, words) }.asInstanceOf[ServiceImplementation[C]] } // typed by its class

  /** The same, typed by the service `T` the class implements. */
  private def typed[T: Type](q: Quotes, implementing: Any, words: List[Expr[ServiceDeclaration[?]]])(using Quotes)
      : Expr[ServiceImplementation[T]] =
    val plain = Reader(q)
    import plain.q.reflect.*
    val cls = implementing.asInstanceOf[Symbol]
    val trt = implemented(plain)(cls)
    val held = plain.stateFields(cls).filter(f => plain.serviceOf(cls.typeRef.memberType(f)).nonEmpty)
    val asked = s"`lifted[${cls.name}](${held.map(_.name).mkString(", ")})`"
    if held.size != words.size then report.errorAndAbort(s"FrFlow: ${cls.name} holds ${held.size} services and " +
      s"is given ${words.size} words: give the word of each, in order ($asked)")
    held.zip(words).foreach((f, w) => plain.serviceOf(cls.typeRef.memberType(f)).get.typeRef.asType match
      case '[s] => if !(w.asTerm.tpe <:< TypeRepr.of[ServiceDeclaration[s]]) then report.errorAndAbort(
        s"FrFlow: ${cls.name} holds ${f.name}, a ${Type.show[s]}, and is given ${w.show}, which is no word of " +
          s"that service ($asked)"))
    val wiring = held.zip(words).map((f, w) => f.name -> (w: Expr[Any])).toMap
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
    val trt = implemented(plain)(cls)
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
        "(`limits.holding(SpendLimits(…))`)", other)

  /** The service a class implements. */
  private def implemented(r: Reader)(cls: r.q.reflect.Symbol): r.q.reflect.Symbol =
    r.serviceOf(cls.typeRef).filter(_ => r.isImplementation(cls.typeRef)).getOrElse(r.q.reflect.report
      .errorAndAbort(s"FrFlow: ${cls.name} implements no service: a trait that is one of Scala's `caps.Mutable`"))

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
