package frflow.protocol
package obligation

import io.circe.Codec

/** A contract's code tested against it, not proven: how many cases, from which seed, against what (the contract, or the
  * proven define the code runs beside); the case that failed, shrunk; how often each part of the contract held; and
  * what to know about how the cases were made.
  */
final case class TestReport(cases: Int, seed: Long, against: String, failure: Option[TestFailure] = None,
    coverage: List[Covered] = Nil, notes: List[String] = Nil) derives Codec.AsObject:
  /** The parts of the contract no case reached: a test that passes without reaching them says little. */
  def unreached: List[Covered] = coverage.filter(_.held == 0)
  def passed: Boolean = failure.isEmpty && unreached.isEmpty
