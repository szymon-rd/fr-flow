package frflow.testing.report

import frflow.testing.Seed

/** What testing a node's code found: how many cases were asked and tried from which seed, what was tested, what was
  * found (`Outcome`), the targets no case reached, and the notes (each given generator and what it makes, the
  * examples' values one never makes, nothing to vary).
  */
final case class TestReport(count: Count, seed: Seed, against: Against, outcome: Outcome, unreached: List[Target],
    notes: List[Note]):
  /** The cases tried. */
  def cases: Int = count.tried

  def failure: Option[Failure] = outcome match
    case Outcome.Failed(f) => Some(f)
    case _                 => None

  /** The generators given, with what the developer said each makes. */
  def made: List[Made] = notes.collect { case Note.Given(m) => m }
