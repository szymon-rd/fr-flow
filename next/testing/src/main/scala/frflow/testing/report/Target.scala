package frflow.testing.report

/** One thing a test must reach: a part, by its position, and how. */
final case class Target(at: Position, reach: Reach)
