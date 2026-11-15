package frflow.runs

import frflow.{Call as _, *}
import frflow.dsl.term.Term as Said
import scala.annotation.unused
import scala.quoted.*

// Real code in a statement. A method, function or constructor applied to the statement's terms is written as the
// code is (`s.add(x)`, `supervised(body)`), typed against the real classes, and read as the call it is: named as
// the tree read from the code's TASTy names the method. It is never run.

/** Raised if code written in a statement is run: it is only read. */
final class NotRun extends IllegalStateException("code written in a statement is read as a call, never run")

/** Where code is written in a statement, a term stands for the value the code takes. */
object InCode:
  given objectInCode[C](using @unused st: Stating): Conversion[Obj[C], C] = _ => throw NotRun()
  given truthInCode(using @unused st: Stating): Conversion[Said[Boolean], Boolean] = _ => throw NotRun()
  given numberInCode(using @unused st: Stating): Conversion[Said[BigInt], Int] = _ => throw NotRun()
  given textInCode(using @unused st: Stating): Conversion[Said[String], String] = _ => throw NotRun()

extension [A](code: Obj[() => A])
  /** The code where code takes it unevaluated (a by-name argument): `h.startThread(code.byName)`. */
  def byName(using @unused st: Stating): A = throw NotRun()

/** The call the code written is: `call(s.add(x))`. Where a word of a call follows the code (`s.add(x).atomic`), the
  * code is read so without it.
  */
inline def call[A](inline code: A): Call[A] = ${ CodeMacros.call[A]('code) }

implicit inline def codeAsCall[A](inline code: A): Call[A] = ${ CodeMacros.call[A]('code) }

object CodeMacros:
  def call[A: Type](code: Expr[A])(using Quotes): Expr[Call[A]] = Reading().call(code)

  private final class Reading(using val q: Quotes):
    import q.reflect.*

    def call[A: Type](code: Expr[A]): Expr[Call[A]] =
      val (method, on, args) = applied(bare(code.asTerm), Nil)
      val what = frflow.dsl.compiled.source.MemberName.of(method).mkString(" ")
      val takes = (on.toList ++ args).map(thing)
      '{ Call.of[A](${ Expr(what) }, ${ Varargs(takes) }*) }

    /** The tree without what the compiler wraps it in. */
    private def bare(t: Term): Term = t match
      case Inlined(_, Nil, inner) => bare(inner)
      case Typed(inner, _)        => bare(inner)
      case Block(Nil, inner)      => bare(inner)
      case other                  => other

    /** What is called, what it is called on (an object of the statement), and what it takes, in order. */
    private def applied(t: Term, taken: List[Term]): (Symbol, Option[Term], List[Term]) = t match
      case Apply(f, args)                      => applied(bare(f), args.map(bare) ++ taken)
      case TypeApply(f, _)                     => applied(bare(f), taken)
      case Select(New(_), _)                   => (t.symbol, None, taken)
      case Select(on, _) if t.symbol.isDefDef  => (t.symbol, Some(bare(on)).filterNot(static), taken)
      case Ident(_) if t.symbol.isDefDef       => (t.symbol, None, taken)
      case _ => report.errorAndAbort(s"A call in a statement is a method, function or constructor applied: ${t.show}")

    /** A package, or an object whose methods are called on no object of the statement. */
    private def static(on: Term): Boolean =
      on.symbol.exists && (on.symbol.isPackageDef || on.symbol.flags.is(Flags.Module))

    /** What the code is given, as the statement has it: a term of the statement, or a constant. */
    private def thing(t: Term): Expr[Said[Thing]] = t match
      case Apply(Select(conversion, "apply"), List(of)) if conversion.tpe <:< TypeRepr.of[Conversion[?, ?]] =>
        thing(bare(of))
      case Apply(Apply(TypeApply(byName, _), List(of)), _) if byName.symbol.name == "byName" => thing(bare(of))
      case Literal(BooleanConstant(b)) => '{ summon[AsThing[Boolean]](if ${ Expr(b) } then True else False) }
      case Literal(IntConstant(i))     => '{ summon[AsThing[BigInt]](Lift.number(BigInt(${ Expr(i) }))) }
      case Literal(StringConstant(s))  => '{ summon[AsThing[String]](Lift.text(${ Expr(s) })) }
      case Literal(UnitConstant())     => '{ summon[AsThing[Unit]](Lift.unit) }
      case _ => t.asExpr match
        case '{ $term: Said[a] } => Expr.summon[AsThing[a]] match
          case Some(as) => '{ $as($term) }
          case None     => report.errorAndAbort(s"A call in a statement cannot be given a ${Type.show[a]}: ${t.show}")
        case _ => report.errorAndAbort(s"A call in a statement is given terms and constants, not ${t.show}")

  /** Constants as terms. */
  object Lift:
    def number(n: BigInt): Said[BigInt] = n
    def text(s: String): Said[String] = s
    def unit: Said[Unit] = ()
