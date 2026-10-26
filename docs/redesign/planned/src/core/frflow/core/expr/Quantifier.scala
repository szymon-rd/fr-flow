package frflow.core.expr

/** `∀`, `∃`, or `always` (every value that can occur: made, for a domain type; reached, for the models' worlds):
  * specification only; the Scala denotation runs none (a test samples them).
  */
enum Quantifier:
  case Forall, Exists, Always
