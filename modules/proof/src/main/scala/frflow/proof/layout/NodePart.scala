package frflow.proof.layout

/** The modules of a node: what it states, what automation proves, its composition, its code's proof, its
  * other obligations (`Checks`), its tries, and its examples evaluated.
  */
enum NodePart:
  case Spec, Auto, Theorems, Impl, Checks, Tries, Eval
