package frflow
package term

/** `a ==> b` between plain Booleans, as plain code checks them; between terms it is `Term`'s (re-exported by `frflow`). */
object Implication:
  extension (a: Boolean) infix def ==>(b: => Boolean): Boolean = !a || b
