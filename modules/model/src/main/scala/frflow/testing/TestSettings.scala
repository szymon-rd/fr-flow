package frflow
package testing

/** How many cases a contract's code is tested on, and from which seed: the same seed, the same cases. */
final case class TestSettings(cases: Int = 1000, seed: Long = 1)

object TestSettings:
  /** `settings`, with the seed `check` is given (`FRFLOW_SEED`): a number, or `fresh` (a new one for the run, shown in
    * the report). CI runs the fixed seed, then a fresh one: what the fixed one keeps passing, a fresh one may still find.
    */
  def inForce(settings: TestSettings, seed: Option[String]): TestSettings = seed.map(_.trim) match
    case Some("fresh")                           => settings.copy(seed = fresh)
    case Some(s) if s.toLongOption.isDefined      => settings.copy(seed = s.toLong)
    case _                                       => settings
  /** One fresh seed per run: what a result's key and the run itself agree on. */
  private lazy val fresh: Long = System.nanoTime
