package frflow.api.view.whole

import frflow.api.node.lean.ObligationState
import frflow.eval.run.OnCode

/** An example as checked: against the claims (Lean's outcome of `example_<set>_<i>` and of its opposite, or Scala
  * only), and against the code; what it comes to, `outcome`.
  */
final case class ExampleView(name: String, onClaims: OnClaims, onCode: OnCode):
  def outcome: ExampleOutcome =
    if ExampleView.failsOnCode(onCode) || onClaims.contradicted then ExampleOutcome.Fails
    else if onClaims.shown && onCode == OnCode.Holds then ExampleOutcome.Passes
    else ExampleOutcome.Undecided

object ExampleView:
  /** An example's theorem is a try: Lean shows it (or proves it, by the developer's file), or does not. */
  def shown(state: ObligationState): Boolean = state == ObligationState.Shown || state == ObligationState.Proven

  /** The code gives another answer, cannot be run on it, throws, or is given a value no rule allows. A fact only
    * about Declarations (`Abstract`) is the claims' to decide.
    */
  def failsOnCode(c: OnCode): Boolean = c match
    case OnCode.Holds | OnCode.Abstract(_) => false
    case _                                 => true
