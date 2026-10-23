package frflow
package check

import cats.effect.{IO, Resource}
import cats.syntax.all.*
import frflow.lean.*
import frflow.protocol.{NodeKind as _, *}
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.Files

/** The goal an obligation leaves after the first steps of a proof by hand (`Generate.recipe`), as Lean
  * prints it: what `scaffold` writes in a stub, and `check` prints when automation gave up, so the agent
  * starts from the state its own first steps give.
  */
object ProofState:
  /** The goal, or none when Lean cannot say. */
  def of(lake: Lake, kb: KnowledgeBase, g: Generate, n: Node[?], o: String): IO[Option[String]] =
    Resource.make(IO.blocking(Files.createTempFile("frflow-state", ".lean")))(f => IO.blocking(Files.deleteIfExists(f)).void).use { file =>
      IO.blocking(Files.writeString(file, source(kb, g, n, o), UTF_8)) *>
        lake.elaborate(file.toString).map(goal(_, file.getFileName.toString))
    }

  /** A file proving the obligation by its first steps alone. */
  def source(kb: KnowledgeBase, g: Generate, n: Node[?], o: String): String =
    val ns = s"${kb.name}.${n.id}"
    s"import ${g.specModule(n.id)}\n\nset_option autoImplicit false\nset_option linter.unusedVariables false\n" +
      s"noncomputable section\nopen Classical\n\nnamespace $ns.State\nopen $ns\n\ntheorem state : Obl.$o := by\n  " +
      Generate.recipe(o).mkString("\n  ") + s"\n  done\n\nend $ns.State\n"

  /** What Lean said of that file: the unsolved goals, or that the steps prove it. */
  def goal(run: Run, fileName: String): Option[String] =
    val errs = Lean.diagnostics(run.output).filter(d => d.isError && d.file.endsWith(fileName))
    errs.find(_.message.startsWith("unsolved goals")).map(_.message.stripPrefix("unsolved goals").trim)
      .orElse(Option.when(errs.isEmpty && run.ok)("no goals: these steps prove it"))

  def text(o: String, state: String): String =
    s"After `${Generate.recipe(o).mkString("; ")}` (the first steps the stub has), the goal is:\n$state"

/** Creates the proof file of a node with a stub for each obligation the last check left open. */
object Scaffold:
  /** The proof file written (its path under the project), or none when there was nothing to add. */
  def apply(a: Analysis, lake: Lake, n: Node[?]): IO[Option[String]] =
    val g = a.generate
    val rel = g.proofsPath(n.id)
    val add = stubs(a, n)
    // Each stub shows, as a comment, the goal its first steps leave: the state `check` prints.
    val states: IO[Map[String, Option[String]]] =
      lake.available.ifM(lake.build(g.specModule(n.id)).map(_.ok), IO.pure(false))
        .flatMap(built => if !built then IO.pure(Map.empty) else add.traverse(o => ProofState.of(lake, a.kb, g, n, o).tupleLeft(o)).map(_.toMap))
    if add.isEmpty then IO.pure(None)
    else states.flatMap { st =>
      text(a, n, add, o => st.get(o).flatten.fold("")(comment))
        .traverse(t => Disk.update(a.ws.lean.resolve(rel), t))
        .map(_.filter(identity).map(_ => s"lean/$rel"))
    }

  /** The obligations to stub: those the last check left open (`complete`, the implementation, a check...),
    * or `complete` before any check; less those the proof file already has.
    */
  def stubs(a: Analysis, n: Node[?]): List[String] =
    val g = a.generate
    val names = g.obligations(n).map(_.name)
    val open = a.checks.get(NodeId(n.id)).toList.flatMap(_.obligations)
      .filter(r => r.status == ObligationStatus.Open || r.status == ObligationStatus.Failed).map(_.name).filter(names.contains)
    val wanted = if open.nonEmpty then open else g.obligation(n, "complete").map(_.name).toList
    val existing = a.proofOf(n).fold(List.empty[String])(src => Lean.theorems(src).map(_.name))
    wanted.filterNot(existing.contains)

  /** The proof file with the stubs added (created if missing); none when its end is not found. */
  def text(a: Analysis, n: Node[?], add: List[String], state: String => String): Option[String] =
    a.proofOf(n) match
      case None => Some(a.generate.proofFile(n, add, state))
      case Some(src) =>
        val i = src.lastIndexOf(s"end ${a.kb.name}.${n.id}.Proofs")
        Option.when(i >= 0)(src.substring(0, i) + a.generate.stubs(add, state) + src.substring(i))

  private def comment(st: String): String =
    s"  /- The goal here (as `check` prints it when automation gives up):\n${st.replace("-/", "- /").linesIterator.map("     " + _).mkString("\n")}\n  -/\n"
