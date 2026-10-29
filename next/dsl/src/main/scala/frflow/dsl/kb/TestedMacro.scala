package frflow.dsl.kb

import frflow.core.term.Program
import frflow.dsl.vocab.Definition as Defined
import scala.quoted.*

/** `implementTested(ds*)` read at compile time: the type of the first Definition (what plain Scala given it alone is
  * typed by) and the shape of each (`Shape`), so the Scala given operations on a state is typed by their
  * Definitions (`Tested`).
  */
object TestedMacro:
  def of(kb: Expr[FrModel], ds: Expr[Seq[Defined[?]]])(using Quotes): Expr[Any] =
    import quotes.reflect.*
    val each = ds match
      case Varargs(es) => es.toList
      case _           => report.errorAndAbort("FrFlow: implementTested is given its Definitions one by one")
    val types = each.map(e => meant(e.asTerm.tpe))
    val shapes = types.foldRight(TypeRepr.of[EmptyTuple])((t, rest) =>
      TypeRepr.of[*:].appliedTo(List(shape(t), rest)))
    (types.headOption.getOrElse(report.errorAndAbort("FrFlow: implementTested is given a Definition")).asType,
      shapes.asType) match
      case ('[f], '[type s <: Tuple; s]) => '{ Tested[f, s]($kb, List(${ Varargs(each) }*)) }
      case _                             => report.errorAndAbort("FrFlow bug: the operations' shapes are no tuple")

  /** `A` of a `Definition[A]`. */
  private def meant(using Quotes)(t: quotes.reflect.TypeRepr): quotes.reflect.TypeRepr =
    import quotes.reflect.*
    t.widen.baseType(TypeRepr.of[Defined].typeSymbol) match
      case AppliedType(_, List(a)) => a
      case other                   => report.errorAndAbort(s"FrFlow: ${other.show} is no Definition")

  /** An operation's shape: `Op1[A, R]` of `A => Program[R]`; `NotAnOperation[T]` of any other type. */
  private def shape(using Quotes)(t: quotes.reflect.TypeRepr): quotes.reflect.TypeRepr =
    import quotes.reflect.*
    val program = TypeRepr.of[Program].typeSymbol
    def result(r: TypeRepr): Option[TypeRepr] = r.dealias match
      case AppliedType(c, List(x)) if c.typeSymbol == program => Some(x)
      case _                                                    => None
    val ops = List(TypeRepr.of[Shape.Op0], TypeRepr.of[Shape.Op1], TypeRepr.of[Shape.Op2], TypeRepr.of[Shape.Op3],
      TypeRepr.of[Shape.Op4], TypeRepr.of[Shape.Op5], TypeRepr.of[Shape.Op6])
    val (ins, out) = t.dealias match
      case f @ AppliedType(_, args) if f.isFunctionType => (args.init, result(args.last))
      case other                                        => (Nil, result(other))
    out.filter(_ => ins.size < ops.size).fold(TypeRepr.of[Shape.NotAnOperation].appliedTo(t))(r =>
      ops(ins.size).appliedTo(ins :+ r))
