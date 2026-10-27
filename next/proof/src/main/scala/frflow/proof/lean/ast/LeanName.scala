package frflow.proof.lean.ast

import cats.{Order, Show}

/** An identifier as Lean reads it: escaped (`«by»`) when it is a keyword, renamed (`some_`) when it would capture a
  * name of the prelude. Only `Names` makes one, so every printed identifier is valid and capture-free.
  */
opaque type LeanName = String

object LeanName:
  private[lean] def unsafe(s: String): LeanName = s
  extension (n: LeanName) def text: String = n
  given Order[LeanName] = Order.by(identity[String])
  given Show[LeanName] = Show.show(identity)
