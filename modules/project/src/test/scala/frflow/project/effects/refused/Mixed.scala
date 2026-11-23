package frflow.project.effects.refused

/** A choice between values of two types, its value used. */
final class Mixed:
  def either(c: Boolean): Any =
    val one = if c then 1 else true
    one
