package frflow.dsl.structure

import frflow.core.name.SymbolName
import frflow.dsl.build.{Source, WrittenAt}
import frflow.dsl.term.LeanType
import frflow.dsl.term.Term as DTerm
import frflow.dsl.vocab.Declaration
import frflow.dsl.vocab.Definition as Defined
import scala.quoted.*

/** `Declaration[T]("…")` of a structure: a trait of the developer's whose methods are the structure's members. The
  * word is typed by them, each taking terms and giving a `Call`, so a statement calls a member as the trait
  * declares it; and by what its states are typed by (`State`). Of any other type, the word `vocab.Declaration`
  * makes.
  */
object Declaring:
  /** `Declaration[A]("…")` as the facade has it. */
  transparent inline def apply[A](inline means: String): Declaration[A] =
    ${ StructureMacros.declared[A]('{ SymbolName(Source.valName) }, 'means, '{ WrittenAt.in(Source.here) }) }

object StructureMacros:
  def declared[A: Type](name: Expr[SymbolName], means: Expr[String], at: Expr[WrittenAt])(using Quotes)
      : Expr[Declaration[A]] =
    import quotes.reflect.*
    if !isStructure(TypeRepr.of[A]) then '{ (Defined.plain[A]($name, $means, $at): Declaration[A]) }
    else structure[A](name, means, at)

  /** Whether a type is a structure: a trait of the developer's that is one of Scala's `caps.Mutable` (a member
    * marked `update` changes it); or one that is not, so no member changes it, that is open, has members, each over
    * domain types, and is no domain type itself.
    */
  def isStructure(using Quotes)(t: quotes.reflect.TypeRepr): Boolean =
    import quotes.reflect.*
    structured(t, (of: TypeRepr) => of.asType match
      case '[x] => Expr.summon[LeanType[x]].nonEmpty)

  /** The same, `domain` saying which types are domain types: inside a compilation the compiler's search for a
    * `LeanType` says; where a compiled class is read, the companions' specs do.
    */
  def structured(using Quotes)(t: quotes.reflect.TypeRepr, domain: quotes.reflect.TypeRepr => Boolean): Boolean =
    import quotes.reflect.*
    val c = t.typeSymbol
    def unchanging: Boolean = !c.flags.is(Flags.Sealed) && !domain(t) && members(t).nonEmpty &&
      members(t).forall((_, inputs, result) => (result :: inputs).forall(domain))
    c.isClassDef && c.flags.is(Flags.Trait) && !List("scala.", "java.").exists(c.fullName.startsWith) &&
      (t.baseClasses.exists(_.fullName == "scala.caps.Mutable") || unchanging)

  /** A structure's members: its abstract methods, its own in the order it declares them and then those it inherits,
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

  private def structure[A: Type](name: Expr[SymbolName], means: Expr[String], at: Expr[WrittenAt])(using Quotes)
      : Expr[Declaration[A]] =
    import quotes.reflect.*
    val t = TypeRepr.of[A]
    val all = described(t)
    refined(t).asType match
      case '[d] => '{ new StructureDeclaration[A]($name, $means, $at, $all)(using
        State.typed[A](${ Expr(t.typeSymbol.name) })).asInstanceOf[d & Declaration[A]] }

  /** The structure's members as the Definition keeps them: each one's name, whether it changes the structure, and the
    * domain types of its inputs and its result.
    */
  private def described(using Quotes)(t: quotes.reflect.TypeRepr): Expr[List[Member]] =
    import quotes.reflect.*
    def leanType(of: TypeRepr): Expr[LeanType[?]] = of.asType match
      case '[x] => Expr.summon[LeanType[x]].getOrElse(report.errorAndAbort(s"FrFlow: the structure " +
        s"${t.typeSymbol.name} has a member over ${of.show}, which is no domain type: derive an FrSpec for it"))
    Expr.ofList(members(t).map((m, inputs, result) =>
      '{ Member(${ Expr(m.name) }, ${ Expr(m.flags.is(Flags.Mutable)) }, ${ Expr.ofList(inputs.map(leanType)) },
        ${ leanType(result) }) }))

  /** The Definition's type: its states typed by the structure's name (`State`), and a member for each of the
    * structure's, taking terms and giving a `Call`.
    */
  private def refined(using Quotes)(t: quotes.reflect.TypeRepr): quotes.reflect.TypeRepr =
    import quotes.reflect.*
    val (term, call) = (constructor(TypeRepr.of[DTerm[Any]]), constructor(TypeRepr.of[Call[Any, Any]]))
    val state = constructor(TypeRepr.of[State["s"]]).appliedTo(ConstantType(StringConstant(t.typeSymbol.name)))
    t.asType match
      case '[a] =>
        val typed = Refinement(TypeRepr.of[StructureDeclaration[a]], "Is", TypeBounds(state, state))
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
