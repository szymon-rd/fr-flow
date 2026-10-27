package frflow.api.node.tests

/** One thing a test must reach: a part of the formula (or of a model test), by its position, and how. */
final case class Target(path: List[Int], reach: Reach)
