package frflow.api.node.lean

/** What Lean found of one obligation: proven, open, failed; of a try (one-sided), shown or not shown; of an
  * evaluation, not evaluated; not run; out of time.
  */
enum ObligationState:
  case Proven, Open, Failed, Shown, NotShown, Unevaluated, Unchecked, Timeout
