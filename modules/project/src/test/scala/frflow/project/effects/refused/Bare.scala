package frflow.project.effects.refused

/** A call outside the code on no object that is written. */
final class Bare:
  def positive(n: Int): Int =
    require(n > 0)
    n
