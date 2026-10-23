package frflow
package check

import cats.effect.IO
import java.nio.file.Path
import scala.concurrent.duration.*

/** Where a project lives on disk.
  *
  * {{{
  * <root>/IDEA.md               the developer's idea (the project's `idea` file)
  * <root>/lean/                 Lean workspace: FrFlowGen/ (generated), Proofs/ (authored)
  * <root>/.frflow/ledger.json   the developer's decisions (committed)
  * <root>/.frflow/checks.json   check results (derived, not committed)
  * }}}
  *
  * @param kernelPath path of the FrFlow Lean kernel, relative to `lean/`
  */
final case class Workspace(root: Path, kernelPath: String):
  def lean: Path = root.resolve("lean")
  def ledgerFile: Path = root.resolve(".frflow/ledger.json")
  def checksFile: Path = root.resolve(".frflow/checks.json")
  def snapshotFile: Path = root.resolve(".frflow/kb.json")
  def requestsFile: Path = root.resolve(".frflow/requests.json")

/** How checks run, read once from the environment.
  *
  * @param lake    the `lake` executable (`FRFLOW_LAKE`, or `lake` on the PATH)
  * @param timing  print each Lean run with how long it took (`FRFLOW_TIMING`)
  * @param threads how many nodes of a level are checked side by side (`FRFLOW_THREADS`)
  * @param timeout how long one Lean run may take
  * @param sources every source the build compiles (`-Dfrflow.sources`, as the examples' build sets it)
  */
final case class Config(lake: String, timing: Boolean, threads: Int, timeout: FiniteDuration, sources: List[Path])

object Config:
  val default: Config = Config("lake", timing = false, threads = 4, timeout = 900.seconds, sources = Nil)

  def from(env: Map[String, String], props: Map[String, String]): Config =
    Config(
      lake = env.getOrElse("FRFLOW_LAKE", "lake"),
      timing = env.contains("FRFLOW_TIMING"),
      threads = env.get("FRFLOW_THREADS").flatMap(_.toIntOption).getOrElse(Runtime.getRuntime.availableProcessors.min(4)).max(1),
      timeout = default.timeout,
      sources = props.get("frflow.sources").toList.flatMap(_.split(java.io.File.pathSeparator)).filter(_.nonEmpty).map(Path.of(_)))

  /** The configuration of this process. */
  val load: IO[Config] = IO(from(sys.env, sys.props.toMap))
