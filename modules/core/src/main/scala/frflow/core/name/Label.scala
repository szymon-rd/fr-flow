package frflow.core.name

import cats.kernel.Hash
import cats.{Order, Show}

/** What every name of the IR shares: a string inside, a type of its own outside, ordered by its text. */
private[name] trait Label[T](using toString: T =:= String, fromString: String =:= T):
  def apply(s: String): T = fromString(s)
  extension (t: T) def value: String = toString(t)
  given Order[T] = Order.by(toString(_))
  given Hash[T] = Hash.by(toString(_))
  given Show[T] = Show.show(toString(_))
  given Ordering[T] = Order[T].toOrdering
