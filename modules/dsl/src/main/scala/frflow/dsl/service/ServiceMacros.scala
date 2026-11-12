package frflow.dsl.service

import frflow.core.name.SymbolName
import frflow.dsl.build.{Source, WrittenAt}
import frflow.dsl.term.LeanType
import frflow.dsl.term.Term as DTerm
import frflow.dsl.vocab.Definition as Defined
import scala.quoted.*

/** `Definition[T]("…")` of a service: a trait of the developer's that is one of Scala's `caps.Mutable`, whose
  * methods are the service's members. The Definition is typed by them, each taking terms and giving a `Call`, so a
  * statement calls a member as the trait declares it; and by what its states are typed by (`State`). Of any other
  * type, the Definition it always was.
  */
object Defining:
  /** `Definition[A]("…")` as the facade has it: of a service, typed by the trait's members; of any other type, the
    * Definition `vocab.Definition` makes.
    */
  transparent inline def apply[A](inline means: String): Defined[A] =
    ${ ServiceMacros.defined[A]('{ SymbolName(Source.valName) }, 'means, '{ WrittenAt.in(Source.here) }) }

object ServiceMacros:
  def defined[A: Type](name: Expr[SymbolName], means: Expr[String], at: Expr[WrittenAt])(using Quotes)
      : Expr[Defined[A]] =
    import quotes.reflect.*
    if !isService(TypeRepr.of[A]) then '{ Defined.plain[A]($name, $means, $at) }
    else service[A](name, means, at)

  /** Whether a type is a service: a trait of the developer's that is a `caps.Mutable`. */
  def isService(using Quotes)(t: quotes.reflect.TypeRepr): Boolean =
    import quotes.reflect.*
    val c = t.typeSymbol
    c.isClassDef && c.flags.is(Flags.Trait) && !List("scala.", "java.").exists(c.fullName.startsWith) &&
      t.baseClasses.exists(_.fullName == "scala.caps.Mutable")

  /** A service's members: its abstract methods, its own in the order it declares them and then those it inherits,
    * each with its inputs' types and its result's.
    */
  def members(using Quotes)(t: quotes.reflect.TypeRepr)
      : List[(quotes.reflect.Symbol, List[quotes.reflect.TypeRepr], quotes.reflect.TypeRepr)] =
    import quotes.reflect.*
    val own = t.typeSymbol.declaredMethods
    val all = own ++ t.typeSymbol.methodMembers.filterNot(own.contains).sortBy(_.name)
    def theirs(m: Symbol): Boolean = List("scala.", "java.").exists(m.owner.fullName.startsWith)
    all.filter(m => m.flags.is(Flags.Deferred) && !theirs(m)).map { m =>
      t.memberType(m) match
        case MethodType(_, inputs, result) => (m, inputs, result)
        case ByNameType(result)            => (m, Nil, result)
        case result                        => (m, Nil, result)
    }

  private def service[A: Type](name: Expr[SymbolName], means: Expr[String], at: Expr[WrittenAt])(using Quotes)
      : Expr[Defined[A]] =
    import quotes.reflect.*
    val t = TypeRepr.of[A]
    val all = described(t)
    refined(t).asType match
      case '[d] => '{ new ServiceDefinition[A]($name, $means, $at, $all)(using
        State.typed[A](${ Expr(t.typeSymbol.name) })).asInstanceOf[d & Defined[A]] }

  /** The service's members as the Definition keeps them: each one's name, whether it changes the service, and the
    * domain types of its inputs and its result.
    */
  private def described(using Quotes)(t: quotes.reflect.TypeRepr): Expr[List[Member]] =
    import quotes.reflect.*
    def leanType(of: TypeRepr): Expr[LeanType[?]] = of.asType match
      case '[x] => Expr.summon[LeanType[x]].getOrElse(report.errorAndAbort(s"FrFlow: the service " +
        s"${t.typeSymbol.name} has a member over ${of.show}, which is no domain type: derive an FrSpec for it"))
    Expr.ofList(members(t).map((m, inputs, result) =>
      '{ Member(${ Expr(m.name) }, ${ Expr(m.flags.is(Flags.Mutable)) }, ${ Expr.ofList(inputs.map(leanType)) },
        ${ leanType(result) }) }))

  /** The Definition's type: its states typed by the service's name (`State`), and a member for each of the
    * service's, taking terms and giving a `Call`.
    */
  private def refined(using Quotes)(t: quotes.reflect.TypeRepr): quotes.reflect.TypeRepr =
    import quotes.reflect.*
    val (term, call) = (constructor(TypeRepr.of[DTerm[Any]]), constructor(TypeRepr.of[Call[Any, Any]]))
    val state = constructor(TypeRepr.of[State["s"]]).appliedTo(ConstantType(StringConstant(t.typeSymbol.name)))
    t.asType match
      case '[a] =>
        val typed = Refinement(TypeRepr.of[ServiceDefinition[a]], "Is", TypeBounds(state, state))
        members(t).foldLeft(typed) { case (parent, (m, inputs, result)) =>
          val gives = call.appliedTo(List(state, result))
          if inputs.isEmpty then Refinement(parent, m.name, gives)
          else Refinement(parent, m.name, MethodType(inputs.indices.toList.map(i => s"x$i"))(
            _ => inputs.map(i => term.appliedTo(i)), _ => gives))
        }

  private def constructor(using Quotes)(applied: quotes.reflect.TypeRepr): quotes.reflect.TypeRepr =
    import quotes.reflect.*
    applied match
      case AppliedType(c, _) => c
      case other             => other
