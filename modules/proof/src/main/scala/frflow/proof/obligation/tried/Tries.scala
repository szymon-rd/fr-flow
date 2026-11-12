package frflow.proof.obligation.tried

import frflow.core.analysis.resolution.Resolved
import frflow.core.name.NodeId
import frflow.core.spec.NodeKind
import frflow.proof.obligation.{Discharge, Obligation, ObligationName, Prop, TryKind}
import frflow.proof.terms.TermTable

/** What is tried of a node, in today's order and with today's sentences. One-sided: proven, they show something
  * wrong. A split's tries are about the node and all its parts.
  */
object Tries:
  val Heartbeats: Int = 4000

  /** None of a rule: its claim is `True` (it holds of every value as a guard), and that it admits a value is
    * `inhabited_`.
    */
  def of(r: Resolved, table: TermTable, n: NodeId): List[Obligation] =
    if r.theory.node(n).exists(_.statement.rule) then Nil
    else (Splits.of(r, n) ++ says(r, n) ++ List(unsat(n))).map(tried) ++ Idle.of(r, table, n)

  /** Of a claim with no parts, the tautology try (`vacuous`): it holds whatever what it speaks of means, so it says
    * nothing (semantics review, finding 7: `accepted r = accepted r`, or `∀ w, ∃ c, opening w = c`).
    */
  private def says(r: Resolved, n: NodeId): List[(TryKind, Prop, String)] =
    r.theory.node(n).filter(x => x.statement.kind == NodeKind.Claim && x.statement.stated &&
      r.theory.refinement.parts(n).isEmpty).toList.map(_ =>
      (TryKind.Vacuous, Prop.over(List(n), Prop.claim(n)), s"${n.value} holds whatever what it speaks of means."))

  private def tried(k: TryKind, p: Prop, doc: String) =
    Obligation(ObligationName.Tried(k), p, Discharge.Attempt(Heartbeats), doc)

  /** The contradiction search: an early refuter only, proven when nothing meets the claim. Consistency is shown
    * by witnesses (`Joint`), never by this try failing.
    */
  private def unsat(n: NodeId) = (TryKind.Unsat, Prop.over(Nil, Prop.Not(Prop.claim(n))), s"No world meets ${n.value}.")
