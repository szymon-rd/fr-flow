package frflow.proof.lean.ast

/** Lean's infix operators the generated Lean uses, each with its spelling. */
enum LOp(val text: String):
  case And extends LOp("∧")
  case Or extends LOp("∨")
  case Arrow extends LOp("→")
  case Iff extends LOp("↔")
  case Eq extends LOp("=")
  case Ne extends LOp("≠")
  case Add extends LOp("+")
  case Sub extends LOp("-")
  case Mul extends LOp("*")
  case Lt extends LOp("<")
  case Le extends LOp("≤")
  case Gt extends LOp(">")
  case Ge extends LOp("≥")
  case Append extends LOp("++")
  case Cons extends LOp("::")
  case Mem extends LOp("∈")
  case Times extends LOp("×")
