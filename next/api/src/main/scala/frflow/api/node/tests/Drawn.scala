package frflow.api.node.tests

/** Where a case was drawn: its run's seed, its index and its size; the same three draw it again. */
final case class Drawn(seed: Long, index: Int, size: Int)
