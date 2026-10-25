package frflow
package check
package proving

import cats.effect.{IO, Resource}
import frflow.lean.{Generate, LeanOutput, ProofFiles}
import frflow.protocol.*
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.Files

/** The goal an obligation leaves after a proof's first steps (`ProofFiles.recipe`): what `scaffold` stubs and `check` prints. */
object ProofState:
  /** The goal, or none when Lean cannot say. */
  def of(lake: Lake, g: Generate, n: Node[?], o: ObligationName): IO[Option[String]] =
    Resource.make(IO.blocking(Files.createTempFile("frflow-state", ".lean")))(f => IO.blocking(Files.deleteIfExists(f)).void).use { file =>
      IO.blocking(Files.writeString(file, g.goalFile(n, o), UTF_8)) *>
        lake.elaborate(file.toString).map(goal(_, file.getFileName.toString))
    }

  /** What Lean said of that file: the unsolved goals, or that the steps prove it. */
  def goal(run: Run, fileName: String): Option[String] =
    val errs = LeanOutput.diagnostics(run.output).filter(d => d.isError && d.file.endsWith(fileName))
    errs.find(_.message.startsWith("unsolved goals")).map(_.message.stripPrefix("unsolved goals").trim)
      .orElse(Option.when(errs.isEmpty && run.ok)("no goals: these steps prove it"))

  def text(o: ObligationName, state: String): String =
    s"After `${ProofFiles.recipe(o).mkString("; ")}` (the first steps the stub has), the goal is:\n$state"
