package frflow.proof.obligation

import frflow.core.expr.Expr
import frflow.core.name.SymbolName

/** One example or probe as Scala evaluated it (`project` computes it with `eval`): the subject applied to the
  * givens for its open terms, then to the inputs, gives `value`. Each is a closed literal (`Expr.Lit`). Lean is asked
  * to prove it, and not its opposite.
  */
final case class Evaluation(name: ObligationName, subject: Evaluated, givens: Map[SymbolName, Expr],
    inputs: List[Expr], value: Expr)
