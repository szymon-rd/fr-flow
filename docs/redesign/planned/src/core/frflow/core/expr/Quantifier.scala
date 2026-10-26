package frflow.core.expr

/** `∀` or `∃`: specification only; the Scala denotation runs neither (a test samples them). */
enum Quantifier:
  case Forall, Exists
