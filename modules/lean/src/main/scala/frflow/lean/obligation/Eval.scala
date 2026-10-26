package frflow
package lean
package obligation

import frflow.protocol.ObligationName

/** An example evaluated in Lean: `claim` is what Scala computes, and Lean proving `opposite` means the translation is
  * wrong; or, where Scala cannot evaluate the contract (`Against.Answer`), the example's answer, and Lean proving
  * `opposite` means the contract refuses the example.
  */
final case class Eval(name: ObligationName, what: String, claim: String, opposite: String, defs: List[Def[?]] = Nil,
    against: Eval.Against = Eval.Against.Scala)

object Eval:
  /** What Lean's evaluation is held to: Scala's verdict, or the example's answer alone. */
  enum Against:
    case Scala, Answer
