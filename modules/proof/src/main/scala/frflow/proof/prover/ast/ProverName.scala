package frflow.proof.prover.ast

import cats.{Order, Show}

/** An identifier as Lean reads it: escaped (`«by»`) when it is a keyword, renamed (`some_`) when it would capture a
  * name of the prelude. Only `Names` makes one, so every printed identifier is valid and capture-free.
  */
opaque type ProverName = String

object ProverName:
  private[prover] def unsafe(s: String): ProverName = s
  extension (n: ProverName) def text: String = n
  given Order[ProverName] = Order.by(identity[String])
  given Show[ProverName] = Show.show(identity)
