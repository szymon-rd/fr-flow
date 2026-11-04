package frflow.proof.lean.ast

/** Lean's prefix operators, each as generated: a term's negation is written `¬p` (and `-n`), an obligation's `¬ p`. */
enum LPrefix(val text: String):
  case Not extends LPrefix("¬")
  case NotSpaced extends LPrefix("¬ ")
  case Neg extends LPrefix("-")
