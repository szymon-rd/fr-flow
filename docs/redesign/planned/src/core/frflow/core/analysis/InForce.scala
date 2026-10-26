package frflow.core.analysis

import frflow.core.name.NodeId
import frflow.core.Theory

/** Which definition fixes each term, and the terms with several definitions none of which is chosen. Law: a term is
  * in `fixedBy` or in `undecided`, never both, and only if some definition fixes it.
  */
final case class InForce(fixedBy: Map[Fixed, NodeId], undecided: Set[Fixed])

object InForce:
  def of(t: Theory, choice: Choice): InForce =
    val byTerm = t.nodes.flatMap(s => Fixed.of(s.node.statement).map(_ -> s.node.id)).groupMap(_._1)(_._2)
    val picked = byTerm.toList.map((term, ds) => term -> pick(ds, choice))
    val fixed = picked.collect { case (term, Some(d)) => term -> d }.toMap
    InForce(fixed, picked.collect { case (term, None) => term }.toSet)

  private def pick(ds: List[NodeId], choice: Choice): Option[NodeId] = (ds, choice) match
    case (List(d), _)                  => Some(d)
    case (_, Choice.Decided(accepted)) => ds.filter(accepted) match { case List(d) => Some(d); case _ => None }
    case (_, Choice.FirstListed)       => ds.headOption

