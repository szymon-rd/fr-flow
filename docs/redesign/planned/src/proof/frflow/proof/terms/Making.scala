package frflow.proof.terms

import frflow.core.expr.Expr
import frflow.core.name.{SourceText, SymbolName}
import frflow.core.spec.Written
import frflow.core.term.{Bound, Final, Sym, World}
import frflow.core.term.interpret.{Guard, Guarded}
import frflow.core.ty.Ty
import frflow.core.vocab.{OpSig, StateModel}

/** That every result a maker gives meets an `always[T]` (owner §13: where FrFlow covers the code, the value is
  * made meeting it): `∀ inputs, rule (maker inputs)` of a proven define; `∀ inputs w, rule (op inputs w.state)` of a
  * store's operation on its model's state in a world. Its variables come with every `always`'s guard (`Guarded`),
  * so the inputs meet their types' and the world every `always` about it. The maker is applied one input at a time,
  * each cast typed by the maker's type.
  */
object Making:
  def ofDefine(op: SymbolName, ty: Ty, kept: Guard, guards: List[Guard]): Written[Expr] =
    val inputs = ty match
      case Ty.FnOf(ins, _) => ins.zipWithIndex.map((t, i) => s"x$i" -> t)
      case _               => Nil
    Written.formula(Guarded.of(over(inputs, Ty.resultOf(ty), kept)([T[_]] => (s: Sym[T], args: List[T[Any]]) =>
      applied(s, s.param[Any](op, ty), args)), guards), SourceText(s"every result of ${op.value}"))

  /** A store operation's result on its model's state (`model`'s, of type `state`) in a world. */
  def ofModel(m: StateModel, sig: OpSig, kept: Guard, guards: List[Guard]): Written[Expr] =
    val (op, ty) = (SymbolName(sig.name.value), Ty.FnOf(sig.params.map(_._2) :+ m.state, sig.result))
    val made = [T[_]] => (s: Sym[T], args: List[T[Any]]) =>
      applied(s, s.param[Any](op, ty), args.init :+ s.part[Any](args.last.asInstanceOf[T[World]], m.name, m.state))
    Written.formula(Guarded.of(over(sig.params :+ ("w" -> Ty.World), sig.result, kept)(made), guards),
      SourceText(s"every result of ${op.value} on ${m.name.value}"))

  private def over(inputs: List[(String, Ty)], result: Ty, kept: Guard)(
      made: [T[_]] => (Sym[T], List[T[Any]]) => T[Any]): Final[Boolean] = [T[_]] => (s: Sym[T]) =>
    def go(left: List[(String, Ty)], args: List[T[Any]]): T[Boolean] = left match
      case (hint, t) :: rest => s.forall(Bound[Any](hint, t))(x => go(rest, args :+ x))
      case Nil               => kept.of[T, Any](result, s).fold(s.bool(true))(_(made(s, args)))
    go(inputs, Nil)

  /** The maker applied to its inputs one at a time: each a function of the next, by the maker's type. */
  private def applied[T[_]](s: Sym[T], f: T[Any], args: List[T[Any]]): T[Any] =
    args.foldLeft(f)((g, a) => s.app(g.asInstanceOf[T[Any => Any]], a))
