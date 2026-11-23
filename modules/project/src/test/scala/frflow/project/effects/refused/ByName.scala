package frflow.project.effects.refused

/** What is passed by name: evaluated each time it is used, or never. */
final class ByName:
  def twice(x: => Int): Int = x + x
