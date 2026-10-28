package frflow.proof.obligation

import frflow.core.analysis.Resolved
import frflow.core.expr.Exprs
import frflow.core.name.NodeId
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
    else (split(r, n) ++ List(unsat(n))).map(tried) ++ Idle.of(r, table, n)

  private def tried(k: TryKind, p: Prop, doc: String) =
    Obligation(ObligationName.Tried(k), p, Discharge.Attempt(Heartbeats), doc)

  private def split(r: Resolved, n: NodeId): List[(TryKind, Prop, String)] =
    val ps = r.theory.refinement.parts(n)
    def over(body: Prop) = Prop.over(n :: ps, body)
    val clash =
      (TryKind.Clash, over(Prop.Implies(Hyp.parts(ps), Prop.False)), s"The parts of ${n.value} contradict each other.")
    ps match
      case Nil       => Nil
      case List(one) => List(
          (TryKind.Vacuous, over(Prop.claim(n)), s"${n.value} holds whatever ${one.value} says."),
          (TryKind.Restates, over(Prop.Implies(List(Hyp.of(n)), Prop.claim(one))),
            s"${one.value} follows from ${n.value}."),
          clash)
      case _         => ps.map(c => (TryKind.Needed(c), over(Prop.Implies(Hyp.parts(ps.diff(List(c))), Prop.claim(n))),
          s"${n.value} holds without ${c.value}.")) ++ conjuncts(r, n, ps).map((k, p, d) => (k, over(p), d)) :+ clash

  /** Each part against each conjunct, when the claim has as many top-level conjuncts as parts. */
  private def conjuncts(r: Resolved, n: NodeId, ps: List[NodeId]): List[(TryKind, Prop, String)] =
    val cs = r.theory.node(n).flatMap(_.statement.said).fold(Nil)(f => Exprs.conjuncts(f.value))
    if cs.size != ps.size then Nil
    else for { p <- ps; i <- cs.indices.toList.map(_ + 1) }
    yield (TryKind.RestatesConjunct(p, i), Prop.Iff(Prop.claim(p), Prop.ConjunctOf(n, i)),
      s"${p.value} says what conjunct $i of ${n.value} says.")

  /** The contradiction search: an early refuter only, proven when nothing meets the claim. Consistency is shown
    * by witnesses (`Joint`), never by this try failing.
    */
  private def unsat(n: NodeId) = (TryKind.Unsat, Prop.over(Nil, Prop.Not(Prop.claim(n))), s"No world meets ${n.value}.")
