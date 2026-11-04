package frflow.proof.obligation.tried

import frflow.core.analysis.Resolved
import frflow.core.expr.Exprs
import frflow.core.name.NodeId
import frflow.proof.obligation.{Hyp, Prop, TryKind}

/** A split's tries, about the node and all its parts: each part needed, one part not merely restating the node,
  * each part against each conjunct, and the parts not contradicting each other.
  */
object Splits:
  def of(r: Resolved, n: NodeId): List[(TryKind, Prop, String)] =
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
