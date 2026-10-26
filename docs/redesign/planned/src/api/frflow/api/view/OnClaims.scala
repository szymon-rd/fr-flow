package frflow.api.view

import frflow.proof.verdict.ObligationStatus

/** How an example stands against the claims: Lean's status of `example_<i>`, or checked in Scala only (an example
  * that sets values of provided Definitions: Lean is not asked it, so it is not mistaken for a Lean check).
  */
enum OnClaims:
  case Lean(status: ObligationStatus)
  case ScalaOnly
