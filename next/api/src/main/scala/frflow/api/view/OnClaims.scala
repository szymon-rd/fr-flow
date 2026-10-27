package frflow.api.view

import frflow.api.node.lean.ObligationState

/** How an example stands against the claims: Lean's state of `example_<i>`, or checked in Scala only (an example
  * that sets values of provided Definitions: Lean is not asked it, so it is not mistaken for a Lean check).
  */
enum OnClaims:
  case Lean(state: ObligationState)
  case ScalaOnly
