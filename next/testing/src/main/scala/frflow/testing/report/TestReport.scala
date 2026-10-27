package frflow.testing.report

import frflow.testing.Seed
/** What testing a node's code found: how many cases from which seed, what was tested, the smallest failing case, the
  * parts of the formula no case reached, and what each given generator makes.
  */
final case class TestReport(cases: Int, seed: Seed, against: Against, failure: Option[Failure],
    unreached: List[Position], made: List[Made])
