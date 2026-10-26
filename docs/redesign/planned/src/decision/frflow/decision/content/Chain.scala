package frflow.decision.content

import cats.{Eq, Order}

/** The meaning of what a node rests on, as decided: its parents', the definitions' it uses, the callees' it relies on,
  * each with its own chain. A decision is bound to it; when it moves, the decision is under review (`above`).
  */
opaque type Chain = String

object Chain:
  val empty: Chain = ""
  def apply(sha: String): Chain = sha
  extension (c: Chain) def value: String = c
  given Eq[Chain] = Eq.fromUniversalEquals
  given Order[Chain] = Order.fromOrdering(using Ordering.String)
