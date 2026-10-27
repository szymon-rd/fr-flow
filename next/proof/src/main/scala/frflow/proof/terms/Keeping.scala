package frflow.proof.terms

import frflow.core.expr.Expr
import frflow.core.name.{SourceText, SymbolName}
import frflow.core.spec.Written
import frflow.core.term.{Bound, Final, Program, Sym, World}
import frflow.core.term.interpret.{Guard, Guarded}
import frflow.core.ty.Ty

/** That every run of a program keeps what always holds: `∀ inputs before, every guard → match op inputs before with
  * | (_, after) => kept after`. Its variables come with every `always`'s guard (`Guarded`), so the run starts from a
  * world meeting all of them, on inputs meeting their types'; it ends in one meeting this one. Of a program that may
  * fail, a run that fails ends in one too (`Worlds.fails`): the world it leaves is the next run's. The program is
  * applied to its inputs one at a time, each cast typed by the Definition's type (`ty`).
  */
object Keeping:
  def formula(op: SymbolName, ty: Ty, inputs: List[(String, Ty)], kept: Guard, guards: List[Guard])
      : Written[Expr] =
    Written.formula(Guarded.of(run(op, ty, inputs, kept), guards), SourceText(s"every run of ${op.value}"))

  private def run(op: SymbolName, ty: Ty, inputs: List[(String, Ty)], kept: Guard): Final[Boolean] =
    [T[_]] => (s: Sym[T]) =>
      def over(left: List[(String, Ty)], args: List[T[Any]]): T[Boolean] = left match
        case (hint, t) :: rest => s.forall(Bound[Any](hint, t))(x => over(rest, args :+ x))
        case Nil               => s.forall(Bound[World]("before", Ty.World))(before =>
          val called = args.foldLeft(s.param[Any](op, ty))((f, a) => s.app(f.asInstanceOf[T[Any => Any]], a))
            .asInstanceOf[T[Program[Any]]]
          val after = Bound[World]("after", Ty.World)
          val ok = s.runs(called, before, Bound[Any]("result", Ty.yields(Ty.resultOf(ty))), after)((_, w) =>
            holds(s, kept, w))
          Ty.errorOf(ty).fold(ok)(e => s.and(ok, s.fails(called, before, Bound[Any]("error", e), after)((_, w) =>
            holds(s, kept, w)))))
      over(inputs, Nil)

  private def holds[T[_]](s: Sym[T], kept: Guard, w: T[World]): T[Boolean] =
    kept.of[T, World](Ty.World, s).fold(s.bool(true))(_(w))
