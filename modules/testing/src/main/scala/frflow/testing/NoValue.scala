package frflow.testing

import frflow.core.analysis.Constrained
import frflow.core.code.Code
import frflow.core.Theory
import frflow.eval.EvalError

/** Why a statement or an example has no Scala value at all, whatever the values it is given: it quantifies over a
  * type, or reads a Declaration, or a value provided where the code runs that nothing gives it. It is checked in
  * Lean only; any other `EvalError` is a fault of the code or of its wiring.
  */
object NoValue:
  def of(t: Theory, e: EvalError): Boolean = e match
    case EvalError.Quantified => true
    case EvalError.Unbound(s) => t.vocabulary.symbol(s).isDefined &&
        (Constrained.isDeclaration(t, s) || t.code.attached.get(s).forall(_.code == Code.Provided))
    case _                    => false
