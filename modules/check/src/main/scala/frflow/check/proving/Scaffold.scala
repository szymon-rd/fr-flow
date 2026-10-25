package frflow
package check
package proving

import cats.effect.IO
import cats.syntax.all.*
import frflow.lean.LeanSource
import frflow.protocol.*

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
    def comment(st: String) =
      s"  /- The goal here (as `check` prints it when automation gives up):\n${st.replace("-/", "- /").linesIterator.map("     " + _).mkString("\n")}\n  -/\n"
    // The proof file with the stubs added (created if missing); none when its end is not found.
    def text(state: ObligationName => String) = a.proofOf(n) match
      case None => Some(g.proofFile(n, add, state))
      case Some(src) =>
        val i = src.lastIndexOf(s"end ${a.kb.name}.${n.id}.Proofs")
        Option.when(i >= 0)(src.substring(0, i) + g.stubs(add, state) + src.substring(i))
    if add.isEmpty then IO.pure(None)
    else states.flatMap(st => text(o => st.get(o).flatten.fold("")(comment))
      .traverse(t => Disk.update(a.ws.lean.resolve(rel), t)).map(_.filter(identity).map(_ => s"lean/$rel")))

  /** Those the last check left open, or `complete` before any check; less those the proof file has. */
  def stubs(a: Analysis, n: Node[?]): List[ObligationName] =
    val g = a.generate
    val names = g.obligations(n).map(_.name)
    val last = a.checks.get(NodeId(n.id))
    val open = last.toList.flatMap(_.obligations)
      .filter(r => r.status == ObligationStatus.Open || r.status == ObligationStatus.Failed).map(_.name).filter(names.contains)
    val wanted = if last.isDefined then open else g.obligation(n, ObligationName.Complete).map(_.name).toList
    val existing = a.proofOf(n).fold(List.empty[String])(src => LeanSource.theorems(src).map(_.name))
    wanted.filterNot(o => existing.contains(o.lean))
