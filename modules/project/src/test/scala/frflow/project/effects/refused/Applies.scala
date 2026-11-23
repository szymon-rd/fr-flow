package frflow.project.effects.refused

/** A function made where it is used. */
final class Applies:
  def twice(n: Int): Int =
    val double = (x: Int) => x + x
    double(n)
