package frflow.project.effects.refused

/** A field evaluated when it is first read. */
final class Later:
  private var n: Int = 0
  lazy val once: Int = { n = n + 1; n }
