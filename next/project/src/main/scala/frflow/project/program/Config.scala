package frflow.project.program

import frflow.project.process.{Command, Output}
import frflow.testing.{Seed, Settings}
import java.nio.file.Path
import scala.concurrent.duration.FiniteDuration

/** How FrFlow runs, read once from the environment where the shell starts: Lean's build tool and how long one build
  * may take (`FRFLOW_LAKE`), FrFlow's Lean library as the project's `lakefile.toml` requires it (relative to
  * `lean/`), the developer's signing key (`FRFLOW_KEY`, or `~/.config/frflow/signing.key`), and how the tests run
  * (`FRFLOW_SEED`: a number, or `fresh` for the run's own).
  */
final case class Config(lake: Command, library: String, key: Path, tests: Settings)

object Config:
  def of(env: Map[String, String], home: Path, library: String, fresh: Seed): Config = Config(
    Command(env.getOrElse("FRFLOW_LAKE", "lake"), FiniteDuration(900, "seconds"), Output.Merged), library,
    env.get("FRFLOW_KEY").map(_.trim).filter(_.nonEmpty).fold(home.resolve(".config/frflow/signing.key"))(Path.of(_)),
    Settings.withSeed(Settings.default, env.get("FRFLOW_SEED"), fresh))
