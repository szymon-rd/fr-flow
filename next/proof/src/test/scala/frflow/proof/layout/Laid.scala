package frflow.proof.layout

import frflow.core.analysis.Resolved
import frflow.core.consistency.Vacuity
import frflow.core.example.Example
import frflow.proof.lean.ast.LeanModule
import frflow.proof.obligation.{Constant, NodeObligations, Obligation, Obligations}
import frflow.proof.terms.TermTable
import frflow.proof.whole.{ExampleGoals, Joint, Possible}

/** A theory's Lean: its nodes' obligations, those of the theory as a whole (with the values a witness search found),
  * and every module `LeanProject` lays out.
  */
final class Laid(r: Resolved, found: Map[Vacuity, List[Constant]], examples: List[Example]):
  lazy val table: TermTable = TermTable.of(r)
  lazy val nodes: List[NodeObligations] = Obligations.of(r, table, Set.empty)
  lazy val whole: List[Obligation] = Joint.of(r) ++ Possible.of(r, found) ++ ExampleGoals.of(r, examples)
  lazy val modules: List[LeanModule] = LeanProject.of(r, table, nodes, whole)
  def obligations: List[Obligation] = nodes.flatMap(o => o.required ++ o.tried) ++ whole
