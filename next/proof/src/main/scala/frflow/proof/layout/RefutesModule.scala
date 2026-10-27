package frflow.proof.layout

import frflow.core.analysis.Resolved
import frflow.core.name.NodeId
import frflow.proof.lean.ast.*
import frflow.proof.lean.lower.{LowerType, LowerValue}
import frflow.proof.lean.term.Printed
import frflow.proof.terms.TermTable

/** A step refuted (today's `Refutation.lean`): the theorem that the node's `complete` is false, given an answer its one
  * part allows (`answer`, a term of the type of what the part's call is about, printed by the term printer) and the
  * case `testing.StepRefutation` found (`case_i`, each value lowered by `LowerValue`). Its tactics are FrFlow's own,
  * applying `complete` to the answer and the case in order: a node whose `complete` is over more open terms than the
  * part's Definition is not confirmed by it (a refutation is one-sided).
  */
object RefutesModule:
  def of(r: Resolved, table: TermTable, node: NodeId, found: Refutation): LeanModule =
    val l = Lowering(r, table)
    val defs = List(Attr.FrflowDefs)
    val (term, ty, inputs) = (found.answer, found.ty, found.inputs)
    val answered = Decl.Def(defs, Names.builtin("answer"), Nil, LowerType.binder(ty),
      Printed.term(l.env, l.naming, 0)(term))
    val cases = inputs.zipWithIndex.map((c, i) => Decl.Def(defs, Names.builtin(s"case_$i"), Nil, LowerType(c.ty),
      LowerValue(l.env)(c.value, c.ty).runA(l.naming).value))
    val refutes = Decl.Theorem(Nil, Names.builtin("refutes"), Nil,
      LExpr.Prefix(LPrefix.NotSpaced, LExpr.Const(Names.path("Obl", "complete"))), Proof.Tactics(List(
        "unfold Obl.complete", "intro h", "have h := h answer (by simp [frflow_defs])",
        ("have h := h" :: inputs.indices.map(i => s"case_$i").toList).mkString(" "), "simp [frflow_defs] at h",
        "all_goals first | omega | grind")), Break.SameLine)
    val m = Imports.onto(l, LeanModule(l.layout.refutes(node), Nil, Preamble.generated,
      Names.path(l.kb.value, node.value, "Refutes"), Nil, (answered :: cases) :+ refutes))
    m.copy(imports = (m.imports :+ l.layout.ofNode(node, NodePart.Spec)).distinct)

