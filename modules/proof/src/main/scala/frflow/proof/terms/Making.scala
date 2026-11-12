package frflow.proof.terms

import frflow.core.expr.Expr
import frflow.core.name.{SourceText, SymbolName}
import frflow.core.spec.Written
import frflow.core.term.Bound
import frflow.core.term.interpret.{Guard, Guarded}
import frflow.core.term.language.{Final, Sym}
import frflow.core.ty.Ty

/** That every result a maker gives meets an `always[T]` (owner §13: where FrFlow covers the code, the value is
  * made meeting it): `∀ inputs, rule (maker inputs)` of a proven define. Its variables come with every `always`'s
  * guard (`Guarded`), so the inputs meet their types'. The maker is applied one input at a time, each cast typed by
  * the maker's type.
  */
object Making:
  def ofDefine(op: SymbolName, ty: Ty, kept: Guard, guards: List[Guard]): Written[Expr] =
    val inputs = ty match
      case Ty.FnOf(ins, _) => ins.zipWithIndex.map((t, i) => s"x$i" -> t)
      case _               => Nil
    Written.formula(Guarded.of(over(inputs, Ty.resultOf(ty), kept)([T[_]] => (s: Sym[T], args: List[T[Any]]) =>
      applied(s, s.param[Any](op, ty), args)), guards), SourceText(s"every result of ${op.value}"))

  /** Of the values from outside, each of a type in `from`: `∀ x, assumed x → rule x`, every assumption of `always`
    * on its type a hypothesis (`Guarded`), the rule at each `T` it holds (`kept`).
    */
  def ofOutside(from: List[Ty], kept: Guard, assumed: List[Guard]): Written[Expr] =
    Written.formula(Guarded.of([T[_]] => (s: Sym[T]) => from.map(ty => s.forall(Bound[Any]("x", ty))(x =>
      kept.of[T, Any](ty, s).fold(s.bool(true))(_(x)))).reduceLeftOption(s.and).getOrElse(s.bool(true)), assumed),
      SourceText("every value from outside"))

  private def over(inputs: List[(String, Ty)], result: Ty, kept: Guard)(
      made: [T[_]] => (Sym[T], List[T[Any]]) => T[Any]): Final[Boolean] = [T[_]] => (s: Sym[T]) =>
    def go(left: List[(String, Ty)], args: List[T[Any]]): T[Boolean] = left match
      case (hint, t) :: rest => s.forall(Bound[Any](hint, t))(x => go(rest, args :+ x))
      case Nil               => kept.of[T, Any](result, s).fold(s.bool(true))(_(made(s, args)))
    go(inputs, Nil)

  /** The maker applied to its inputs one at a time: each a function of the next, by the maker's type. */
  private def applied[T[_]](s: Sym[T], f: T[Any], args: List[T[Any]]): T[Any] =
    args.foldLeft(f)((g, a) => s.app(g.asInstanceOf[T[Any => Any]], a))
