package frflow
package lean

import frflow.protocol.ObligationName

/** The files an agent proves in (`Proofs/<KB>/<Node>.lean`), their stubs, and the Lake project. */
final class ProofFiles(kb: KnowledgeBase, layout: Layout, refinement: Refinement):
  private val K = kb.name

  /** A stub for each obligation, to prove in its place: the first steps of a proof by hand, what they
    * leave (`state`, as a comment, when known), then `sorry`.
    */
  def stubs(names: List[ObligationName], state: ObligationName => String = _ => ""): String =
    names.map(o => s"theorem $o : Obl.$o := by\n  ${ProofFiles.recipe(o).mkString("\n  ")}\n${state(o)}  sorry\n\n").mkString

  /** A proof file with a stub for each of `names` (and for `feasible` with `complete`, unless a proven
    * implementation below witnesses the node).
    */
  def proofFile(n: Node[?], names: List[ObligationName] = List(ObligationName.Complete), state: ObligationName => String = _ => ""): String =
    val all = names ++ Option.when(names.contains(ObligationName.Complete) && !refinement.witnessed(n) && !names.contains(ObligationName.Feasible))(ObligationName.Feasible)
    s"""import ${layout.spec(n.id).name}
       |
       |/-! Authored proofs of the obligations of ${n.id}. Each states exactly its `Obl`. -/
       |
       |${LeanText.Preamble}
       |namespace $K.${n.id}.Proofs
       |open $K.${n.id}
       |
       |""".stripMargin + stubs(all, state) + s"end $K.${n.id}.Proofs\n"

  /** A file asking Lean for the goal obligation `o` of `n` leaves after the first steps of a proof by
    * hand (see `recipe`): Lean reports it as unsolved.
    */
  def goalFile(n: Node[?], o: ObligationName): String =
    val ns = s"$K.${n.id}"
    s"import ${layout.spec(n.id).name}\n\n${LeanText.Preamble}namespace $ns.State\nopen $ns\n\ntheorem state : Obl.$o := by\n  " +
      ProofFiles.recipe(o).mkString("\n  ") + s"\n  done\n\nend $ns.State\n"

  def lakefile(kernelPath: String): String =
    s"""name = "${K.toLowerCase}"
       |defaultTargets = ["FrFlowGen"]
       |
       |[[require]]
       |name = "frflow"
       |path = "$kernelPath"
       |
       |[[lean_lib]]
       |name = "FrFlowGen"
       |globs = ["FrFlowGen.+"]
       |
       |[[lean_lib]]
       |name = "Proofs"
       |globs = ["Proofs.+"]
       |""".stripMargin

object ProofFiles:
  /** The first steps of a proof by hand (the skill's recipe): the obligation unfolded, its binders
    * introduced by their generated names, the generated definitions unfolded everywhere.
    */
  def recipe(o: ObligationName): List[String] = List(s"unfold Obl.$o", "frflow_intro", "simp only [frflow_defs] at *")
