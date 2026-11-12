package frflow.api.view.whole

import frflow.api.node.lean.ObligationView

/** How an example stands against the claims: Rocq's outcome of `example_<set>_<i>` and of its opposite
  * (`…_opposite`, the claims giving its negation), with their messages, or checked in Scala only (an example that
  * sets values of provided Definitions: Rocq is not asked it, so it is not mistaken for a Rocq check).
  */
enum OnClaims:
  case Rocq(check: ObligationView, opposite: ObligationView)
  case ScalaOnly

  /** Rocq shows it, or is not asked it. */
  def shown: Boolean = this match
    case Rocq(c, _) => ExampleView.shown(c.state)
    case ScalaOnly  => true

  /** Rocq shows its opposite: the claims contradict it. */
  def contradicted: Boolean = this match
    case Rocq(_, o) => ExampleView.shown(o.state)
    case ScalaOnly  => false

  /** Rocq shows both it and its opposite: the statements it is shown from cannot all hold (they are inconsistent
    * there), so neither says anything.
    */
  def inconsistent: Boolean = shown && contradicted
