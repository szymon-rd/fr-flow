package frflow.testing

/** How many cases each node's code is tested on, from which seed: the checker's configuration (`project.Config`),
  * since it says how tests run, not what the model states.
  */
final case class Settings(cases: Int, seed: Seed)

object Settings:
  /** 1,000 cases from seed 1, as today's settings. */
  val default: Settings = Settings(1000, Seed(1))

  /** `settings` with the seed `check` is given (`FRFLOW_SEED`): a number, or `fresh` (the run's own, `fresh`);
    * anything else keeps the settings' seed.
    */
  def withSeed(settings: Settings, written: Option[String], fresh: Seed): Settings = written.map(_.trim) match
    case Some("fresh")                       => settings.copy(seed = fresh)
    case Some(s) if s.toLongOption.isDefined => settings.copy(seed = Seed(s.toLong))
    case _                                   => settings
