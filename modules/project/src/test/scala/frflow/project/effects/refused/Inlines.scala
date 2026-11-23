package frflow.project.effects.refused

/** A method Scala puts in place where it is called: what it is given is no value. */
final class Inlines:
  inline def twice(inline x: Int): Int = x + x
