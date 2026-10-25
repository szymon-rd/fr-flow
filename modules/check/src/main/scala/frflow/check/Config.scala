package frflow
package check

import cats.effect.IO
import frflow.ledger.KeyStore
import java.nio.file.Path
import scala.concurrent.duration.*

/** How FrFlow runs, read once from the environment: `FRFLOW_LAKE`, `FRFLOW_TIMING` (print each Lean run's time),
  * `FRFLOW_THREADS` (the nodes of a level checked side by side), the developer's key (`FRFLOW_KEY`, or the one under
  * the home directory), who decides (`FRFLOW_AS`), and `-Dfrflow.sources` (every source the build compiles).
  */
final case class Config(lake: String, timing: Boolean, threads: Int, timeout: FiniteDuration, sources: List[Path], key: Path,
    as: Option[String])

object Config:
  def load(env: Map[String, String]): IO[Config] = IO(Config(
    lake = env.getOrElse("FRFLOW_LAKE", "lake"),
    timing = env.contains("FRFLOW_TIMING"),
    threads = env.get("FRFLOW_THREADS").flatMap(_.toIntOption).getOrElse(Runtime.getRuntime.availableProcessors.min(4)).max(1),
    timeout = 900.seconds,
    sources = sys.props.get("frflow.sources").toList.flatMap(_.split(java.io.File.pathSeparator)).filter(_.nonEmpty).map(Path.of(_)),
    key = KeyStore.keyFile(env, Path.of(sys.props.getOrElse("user.home", "."))),
    as = env.get("FRFLOW_AS").map(_.trim).filter(_.nonEmpty)))

  /** From the process's environment: for the tests. */
  def load: IO[Config] = IO(sys.env).flatMap(load(_))
