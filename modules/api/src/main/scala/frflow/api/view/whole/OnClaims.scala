package frflow.api.view.whole

import frflow.api.node.lean.ObligationView

/** How an example stands against the claims: Lean's outcome of `example_<i>`, with its messages, or checked in Scala
  * only (an example that sets values of provided Definitions: Lean is not asked it, so it is not mistaken for a Lean
  * check).
  */
enum OnClaims:
  case Lean(check: ObligationView)
  case ScalaOnly

  /** Lean shows it, or is not asked it. */
  def shown: Boolean = this match
    case Lean(c)   => ExampleView.shown(c.state)
    case ScalaOnly => true
