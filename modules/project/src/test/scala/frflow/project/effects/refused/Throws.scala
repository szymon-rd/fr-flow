package frflow.project.effects.refused

/** An exception thrown. */
final class Throws:
  def positive(n: Int): Int = if n > 0 then n else throw IllegalArgumentException()
