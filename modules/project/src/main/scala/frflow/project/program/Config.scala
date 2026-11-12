package frflow.project.program

import frflow.project.process.{Command, Output}
import frflow.testing.report.Seed
import frflow.testing.Settings
import java.nio.file.Path
import scala.concurrent.duration.FiniteDuration

/** How FrFlow runs, read once from the environment where the shell starts: Rocq and how long one compile of a module
  * may take (`FRFLOW_ROCQ`), the directory FrFlow's Rocq library is in, the developer's signing key (`FRFLOW_KEY`, else
  * `.config/frflow/signing.key` under `HOME`, both from the environment only: with neither, there is no key), and how
  * the tests run (`FRFLOW_SEED`: a number, or `fresh` for the run's own).
  */
final case class Config(rocq: Command, library: Path, key: Option[Path], tests: Settings)

object Config:
  def of(env: Map[String, String], library: Path, fresh: Seed): Config = Config(
    Command(env.getOrElse("FRFLOW_ROCQ", "rocq"), FiniteDuration(900, "seconds"), Output.ByExit), library,
    keyFile(env), Settings.withSeed(Settings.default, env.get("FRFLOW_SEED"), fresh))

  /** `FRFLOW_KEY`, else the default under `HOME`; none when the environment gives neither. */
  def keyFile(env: Map[String, String]): Option[Path] =
    env.get("FRFLOW_KEY").map(_.trim).filter(_.nonEmpty).map(Path.of(_))
      .orElse(env.get("HOME").map(_.trim).filter(_.nonEmpty).map(h => Path.of(h).resolve(".config/frflow/signing.key")))
