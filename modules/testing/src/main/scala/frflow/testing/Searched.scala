package frflow.testing

import frflow.testing.report.{Hits, Outcome}

/** What one node's cases found: how many were tried, what they reached, and the outcome. */
final case class Searched(tried: Int, hits: Hits, outcome: Outcome)
