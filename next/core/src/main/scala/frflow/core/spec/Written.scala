package frflow.core.spec

import frflow.core.expr.{Binder, Expr, Exprs, Lambda, Prog, Progs}
import frflow.core.name.{SourceText, SymbolName}
import frflow.core.term.{Final, Stated}
import frflow.core.term.interpret.{Retyped, ToExpr}
import frflow.core.ty.Ty

/** An elaborated part with the Scala it was written as: what the back ends read (`form`: the term itself, LNCS 7470
  * §3.2, printed by the Lean printer and run by the evaluator), its initial form (`value`, made from it by `ToExpr`,
  * §3.3: what the analyses read, nothing else), and what the developer decides (`source`). Made only here, so
  * `value` is always `form`'s IR.
  */
final case class Written[+A] private (value: A, source: SourceText, form: Form)

object Written:
  def formula(t: Final[Boolean], source: SourceText): Written[Expr] =
    Written(ToExpr.of(t), source, Form.Term(Stated(t)))

  /** A lambda whose body is a term over its inputs (bound outside it, at levels `0 … n-1`). */
  def lambda[R](inputs: List[Binder], body: Final[R], source: SourceText): Written[Lambda] =
    val e = ToExpr.of(body, inputs.size)
    Written(Lambda(inputs, e, Exprs.typeOf(e)), source, Form.Term(Stated(body)))

  /** A program over its inputs: its recorded steps, their terms over the inputs and the steps' results; the error it
    * may fail with is read off the steps once the boundaries are known (`failing`).
    */
  def steps(inputs: List[Binder], p: Prog[Stated[?]], result: Ty, source: SourceText): Written[Lambda] =
    val ir = Progs.map(p)(s => ToExpr.of(s.run, inputs.size))
    Written(Lambda(inputs, Expr.Do(ir, Ty.FlowOf(result, None)), Ty.FlowOf(result, None)), source, Form.Steps(p))

  extension (w: Written[Expr])
    /** The formula with each symbol at the type `types` gives it (`Retyped`): its term and its IR alike. */
    def retyped(types: SymbolName => Option[Ty]): Written[Expr] = w.form match
      case Form.Term(t)  => formula(Retyped.of(t.run.asInstanceOf[Final[Boolean]], types), w.source) // a formula's
      case Form.Steps(_) => w

  extension (w: Written[Lambda])
    /** A define's body with each symbol at the type `types` gives it; a program's steps as they are. */
    def retypedBody(types: SymbolName => Option[Ty]): Written[Lambda] = w.form match
      case Form.Term(t)  => lambda(w.value.params, Retyped.of(t.run, types), w.source)
      case Form.Steps(_) => w

    /** A program's steps typed with the error its runs may fail with (`analysis.Failing`); anything else as it is. */
    def failing(error: Option[Ty]): Written[Lambda] = w.value.body match
      case Expr.Do(ir, ty) =>
        val typed = Ty.failing(ty, error)
        Written(Lambda(w.value.params, Expr.Do(ir, typed), typed), w.source, w.form)
      case _               => w

  extension (w: Written[Expr])
    /** A formula's term: `formula` made it, so its form is a term of type `Boolean`. */
    def term: Final[Boolean] = w.form match
      case Form.Term(t)  => t.run.asInstanceOf[Final[Boolean]] // made by `formula` only, from a `Final[Boolean]`
      case Form.Steps(_) => throw IllegalStateException("FrFlow bug: a formula made of a program's steps")
