package frflow
package term

/** `a implies b` between plain Booleans, as plain code checks them; between terms it is `Term`'s. */
object Implication:
  extension (a: Boolean) infix def implies(b: => Boolean): Boolean = !a || b
