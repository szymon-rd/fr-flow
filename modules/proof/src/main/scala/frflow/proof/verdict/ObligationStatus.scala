package frflow.proof.verdict

/** What a check found of one obligation: proven, open (not proven), failed; of a try, shown or not shown; of an
  * evaluation, not evaluated.
  */
enum ObligationStatus:
  case Proven, Open, Failed, Shown, NotShown, Unevaluated, Unchecked, Timeout
