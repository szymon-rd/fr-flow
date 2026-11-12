package frflow.core.spec

import frflow.core.expr.{Binder, Expr, Exprs, Lambda}
import frflow.core.name.{SourceText, SymbolName}
import frflow.core.term.interpret.{Retyped, ToExpr}
import frflow.core.term.language.{Final, Stated}
import frflow.core.ty.Ty

/** An elaborated part with the Scala it was written as: what the back ends read (`form`: the term itself, LNCS 7470
  * §3.2, printed by the prover's printer and run by the evaluator), its initial form (`value`, made from it by
  * `ToExpr`, §3.3: what the analyses read, nothing else), and what the developer decides (`source`). Made only here,
  * so `value` is always `form`'s IR.
  */
final case class Written[+A] private (value: A, source: SourceText, form: Form)

object Written:
  def formula(t: Final[Boolean], source: SourceText): Written[Expr] =
    Written(ToExpr.of(t), source, Form.Term(Stated(t)))

  /** A lambda whose body is a term over its inputs (bound outside it, at levels `0 … n-1`). */
  def lambda[R](inputs: List[Binder], body: Final[R], source: SourceText): Written[Lambda] =
    val e = ToExpr.of(body, inputs.size)
    Written(Lambda(inputs, e, Exprs.typeOf(e)), source, Form.Term(Stated(body)))

  extension (w: Written[Expr])
    /** The formula with each symbol at the type `types` gives it (`Retyped`): its term and its IR alike. */
    def retyped(types: SymbolName => Option[Ty]): Written[Expr] = w.form match
      case Form.Term(t) => formula(Retyped.of(t.run.asInstanceOf[Final[Boolean]], types), w.source) // a formula's

    /** A formula's term: `formula` made it, so its form is a term of type `Boolean`. */
    def term: Final[Boolean] = w.form match
      case Form.Term(t) => t.run.asInstanceOf[Final[Boolean]] // made by `formula` only, from a `Final[Boolean]`

  extension (w: Written[Lambda])
    /** A define's body with each symbol at the type `types` gives it. */
    def retypedBody(types: SymbolName => Option[Ty]): Written[Lambda] = w.form match
      case Form.Term(t) => lambda(w.value.params, Retyped.of(t.run, types), w.source)
