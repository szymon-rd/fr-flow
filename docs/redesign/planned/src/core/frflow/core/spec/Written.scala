package frflow.core.spec

import frflow.core.expr.{Binder, Expr, Exprs, Lambda, Prog, Progs}
import frflow.core.name.SourceText
import frflow.core.term.{Final, Stated}
import frflow.core.term.interpret.ToExpr
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

  /** A program over its inputs: its recorded steps, their terms over the inputs and the steps' results. */
  def steps(inputs: List[Binder], p: Prog[Stated[?]], result: Ty, source: SourceText): Written[Lambda] =
    val ir = Progs.map(p)(s => ToExpr.of(s.run, inputs.size))
    Written(Lambda(inputs, Expr.Do(ir, Ty.FlowOf(result)), Ty.FlowOf(result)), source, Form.Steps(p))

  extension (w: Written[Expr])
    /** A formula's term: `formula` made it, so its form is a term of type `Boolean`. */
    def term: Final[Boolean] = w.form match
      case Form.Term(t)  => t.run.asInstanceOf[Final[Boolean]] // made by `formula` only, from a `Final[Boolean]`
      case Form.Steps(_) => throw IllegalStateException("FrFlow bug: a formula made of a program's steps")
