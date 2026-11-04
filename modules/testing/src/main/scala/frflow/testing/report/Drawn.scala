package frflow.testing.report

import frflow.testing.Seed

/** Where a case was drawn: its run's seed, its index and its size; the same three draw it again. */
final case class Drawn(seed: Seed, index: Int, size: Int)
