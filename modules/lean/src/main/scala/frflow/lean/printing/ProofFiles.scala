package frflow
package lean
package printing

import frflow.protocol.ObligationName
import ObligationName.*
import LeanText.*

/** The files proofs are written in (`Proofs/<KB>/<Node>.lean`), their stubs, and the Lake project. */
final class ProofFiles(kb: KnowledgeBase, layout: Layout, refinement: Refinement):
  private val K = kb.name

  /** For each obligation: the first steps of a proof by hand, what they leave (`state`), then `sorry`. */
  def stubs(names: List[ObligationName], state: ObligationName => String = _ => ""): String =
    names.map(o => s"theorem $o : Obl.$o := by\n  ${ProofFiles.recipe(o).mkString("\n  ")}\n${state(o)}  sorry\n\n").mkString

  def proofFile(n: Node[?], names: List[ObligationName] = List(Complete), state: ObligationName => String = _ => ""): String =
    val all = names ++ Option.when(names.contains(Complete) && !refinement.witnessed(n) && !names.contains(Feasible))(Feasible)
    s"""import ${layout.spec(n.id).name}
       |
       |/-! Authored proofs of the obligations of ${n.id}. Each states exactly its `Obl`. -/
       |
       |${Preamble}
       |namespace $K.${n.id}.Proofs
       |open $K.${n.id}
       |
       |""".stripMargin + stubs(all, state) + s"end $K.${n.id}.Proofs\n"

  /** A file whose unsolved goal Lean reports: what `o` leaves after the first steps of a proof by hand. */
  def goalFile(n: Node[?], o: ObligationName): String =
    val ns = s"$K.${n.id}"
    s"import ${layout.spec(n.id).name}\n\n${Preamble}namespace $ns.State\nopen $ns\n\ntheorem state : Obl.$o := by\n  " +
      ProofFiles.recipe(o).mkString("\n  ") + s"\n  done\n\nend $ns.State\n"

  def lakefile(kernelPath: String): String =
    s"name = \"${K.toLowerCase}\"\ndefaultTargets = [\"FrFlowGen\"]\n\n[[require]]\nname = \"frflow\"\npath = \"$kernelPath\"\n\n" +
      List("FrFlowGen", "Proofs").map(l => s"[[lean_lib]]\nname = \"$l\"\nglobs = [\"$l.+\"]\n").mkString("\n")

object ProofFiles:
  def recipe(o: ObligationName): List[String] = List(s"unfold Obl.$o", "frflow_intro", "simp only [frflow_defs] at *")
