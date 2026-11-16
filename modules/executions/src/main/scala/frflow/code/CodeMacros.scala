package frflow.code

import frflow.{Call as _, *}
import frflow.dsl.compiled.source.MemberName
import frflow.dsl.term.Term as Said
import frflow.executions.Call
import frflow.values.{AsValue, Value}
import scala.quoted.*

/** Code written in a statement, read from its typed tree as the call it is. */
object CodeMacros:
  def call[A: Type](code: Expr[A])(using Quotes): Expr[Call[A]] = Reading().call(code)
  def method[C: Type](code: Expr[C => Any])(using Quotes): Expr[String] = Reading().method(code)

  def methods[C: Type](using Quotes): Expr[List[String]] =
    import quotes.reflect.*
    val all = TypeRepr.of[C].typeSymbol.methodMembers.filterNot(_.isClassConstructor)
      .flatMap(m => m :: m.allOverriddenSymbols.toList)
    Expr(all.map(MemberName.of(_).mkString(" ")).distinct.sorted)

  private final class Reading(using val q: Quotes):
    import q.reflect.*

    def call[A: Type](code: Expr[A]): Expr[Call[A]] =
      val (method, on, args) = applied(bare(code.asTerm), Nil)
      val named = MemberName.of(method).mkString(" ")
      val arguments = (on.toList ++ args).map(value)
      '{ Call.of[A](${ Expr(named) }, ${ Varargs(arguments) }*) }

    /** The name of the method a function of one object calls on it. */
    def method[C: Type](code: Expr[C => Any]): Expr[String] = bare(code.asTerm) match
      case Lambda(_, body) => Expr(MemberName.of(applied(bare(body), Nil)._1).mkString(" "))
      case other => report.errorAndAbort(s"A method is named by a call on an object, `_.add(???)`: ${other.show}")

    /** The tree without what the compiler wraps it in. */
    private def bare(t: Term): Term = t match
      case Inlined(_, Nil, inner) => bare(inner)
      case Typed(inner, _)        => bare(inner)
      case Block(Nil, inner)      => bare(inner)
      case other                  => other

    /** What is called, what it is called on (an object of the statement), and its arguments, in order. */
    private def applied(t: Term, taken: List[Term]): (Symbol, Option[Term], List[Term]) = t match
      case Apply(f, args)                      => applied(bare(f), args.map(bare) ++ taken)
      case TypeApply(f, _)                     => applied(bare(f), taken)
      case Select(New(_), _)                   => (t.symbol, None, taken)
      case Select(on, _) if t.symbol.isDefDef  => (t.symbol, Some(bare(on)).filterNot(static), taken)
      case Ident(_) if t.symbol.isDefDef       => (t.symbol, None, taken)
      case _ => report.errorAndAbort(s"A call in a statement is a method, function or constructor applied: ${t.show}")

    /** A package, an object, or a value an object holds for good (`currentScope.get()`): what a call is made on
      * that is no object of the statement. The tree read names such a value alone, and the call takes nothing of it.
      */
    private def static(on: Term): Boolean =
      on.symbol.exists && (on.symbol.isPackageDef || on.symbol.flags.is(Flags.Module) ||
        (on.symbol.isValDef && !on.symbol.flags.is(Flags.Mutable) && on.symbol.owner.flags.is(Flags.Module)))

    /** An argument as the statement has it: a term of the statement, or a constant. */
    private def value(t: Term): Expr[Said[Value]] = t match
      case Apply(Select(conversion, "apply"), List(of)) if conversion.tpe <:< TypeRepr.of[Conversion[?, ?]] =>
        value(bare(of))
      case Apply(Apply(TypeApply(byName, _), List(of)), _) if byName.symbol.name == "byName" => value(bare(of))
      case Literal(BooleanConstant(b)) => '{ summon[AsValue[Boolean]](if ${ Expr(b) } then True else False) }
      case Literal(IntConstant(i))     => '{ summon[AsValue[BigInt]](Lift.number(BigInt(${ Expr(i) }))) }
      case Literal(StringConstant(s))  => '{ summon[AsValue[String]](Lift.text(${ Expr(s) })) }
      case Literal(UnitConstant())     => '{ summon[AsValue[Unit]](Lift.unit) }
      case _ => t.asExpr match
        case '{ $term: Said[a] } => Expr.summon[AsValue[a]] match
          case Some(as) => '{ $as($term) }
          case None     => report.errorAndAbort(s"A call in a statement cannot be given a ${Type.show[a]}: ${t.show}")
        case _ => report.errorAndAbort(s"A call in a statement is given terms and constants, not ${t.show}")

  /** Constants as terms. */
  object Lift:
    def number(n: BigInt): Said[BigInt] = n
    def text(s: String): Said[String] = s
    def unit: Said[Unit] = ()
