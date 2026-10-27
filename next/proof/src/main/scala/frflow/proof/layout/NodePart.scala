package frflow.proof.layout

/** The modules a node's Lean is in: what it states, what automation proves, its composition, its code's proof, its
  * tries and checks, and its examples evaluated.
  */
enum NodePart:
  case Spec, Auto, Theorems, Impl, Checks, Eval
