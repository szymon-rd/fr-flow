package frflow.testing.report

import frflow.testing.Seed

/** What testing a node's code found: how many cases were asked and tried from which seed, what was tested, what was
  * found (`Outcome`), the targets no case reached, and what each given generator makes.
  */
final case class TestReport(count: Count, seed: Seed, against: Against, outcome: Outcome, unreached: List[Target],
    made: List[Made]):
  /** The cases tried. */
  def cases: Int = count.tried

  def failure: Option[Failure] = outcome match
    case Outcome.Failed(f) => Some(f)
    case _                 => None
