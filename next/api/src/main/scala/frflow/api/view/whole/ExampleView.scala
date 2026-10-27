package frflow.api.view.whole

import frflow.api.node.lean.ObligationState
import frflow.eval.run.OnCode

/** An example as checked: against the claims (Lean's outcome of `example_<i>`, or Scala only), and against the code.
  * It passes when the code holds it and Lean shows it, or Lean is not asked it.
  */
final case class ExampleView(name: String, onClaims: OnClaims, onCode: OnCode):
  def passes: Boolean = onCode == OnCode.Holds && onClaims.shown

object ExampleView:
  /** An example's theorem is a try: Lean shows it (or proves it, by the developer's file), or does not. */
  def shown(state: ObligationState): Boolean = state == ObligationState.Shown || state == ObligationState.Proven
