package frflow
package check

import cats.effect.{IO, Resource}
import cats.syntax.all.*
import frflow.lean.*
import frflow.protocol.{NodeKind as _, *}
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.Files

/** The goal an obligation leaves after the first steps of a proof by hand (`ProofFiles.recipe`), as Lean
  * prints it: what `scaffold` writes in a stub, and `check` prints when automation gave up, so the agent
  * starts from the state its own first steps give.
  */
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

/** Creates the proof file of a node with a stub for each obligation the last check left open. */
object Scaffold:
  /** The proof file written (its path under the project), or none when there was nothing to add. */
  def apply(a: Analysis, lake: Lake, n: Node[?]): IO[Option[String]] =
    val g = a.generate
    val rel = g.layout.proofs(n.id).path
    val add = stubs(a, n)
    // Each stub shows, as a comment, the goal its first steps leave: the state `check` prints.
    val states: IO[Map[ObligationName, Option[String]]] =
      lake.available.ifM(lake.build(g.layout.spec(n.id).name).map(_.ok), IO.pure(false))
        .flatMap(built => if !built then IO.pure(Map.empty) else add.traverse(o => ProofState.of(lake, g, n, o).tupleLeft(o)).map(_.toMap))
    if add.isEmpty then IO.pure(None)
    else states.flatMap { st =>
      text(a, n, add, o => st.get(o).flatten.fold("")(comment))
        .traverse(t => Disk.update(a.ws.lean.resolve(rel), t))
        .map(_.filter(identity).map(_ => s"lean/$rel"))
    }

  /** The obligations to stub: those the last check left open (`complete`, the implementation, a check...),
    * or `complete` before any check; less those the proof file already has.
    */
  def stubs(a: Analysis, n: Node[?]): List[ObligationName] =
    val g = a.generate
    val names = g.obligations(n).map(_.name)
    val open = a.checks.get(NodeId(n.id)).toList.flatMap(_.obligations)
      .filter(r => r.status == ObligationStatus.Open || r.status == ObligationStatus.Failed).flatMap(r => ObligationName.parse(r.name)).filter(names.contains)
    val wanted = if open.nonEmpty then open else g.obligation(n, ObligationName.Complete).map(_.name).toList
    val existing = a.proofOf(n).fold(List.empty[String])(src => LeanSource.theorems(src).map(_.name))
    wanted.filterNot(o => existing.contains(o.lean))

  /** The proof file with the stubs added (created if missing); none when its end is not found. */
  def text(a: Analysis, n: Node[?], add: List[ObligationName], state: ObligationName => String): Option[String] =
    a.proofOf(n) match
      case None => Some(a.generate.proofFile(n, add, state))
      case Some(src) =>
        val i = src.lastIndexOf(s"end ${a.kb.name}.${n.id}.Proofs")
        Option.when(i >= 0)(src.substring(0, i) + a.generate.stubs(add, state) + src.substring(i))

  private def comment(st: String): String =
    s"  /- The goal here (as `check` prints it when automation gives up):\n${st.replace("-/", "- /").linesIterator.map("     " + _).mkString("\n")}\n  -/\n"
