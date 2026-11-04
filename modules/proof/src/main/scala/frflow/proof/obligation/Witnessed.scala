package frflow.proof.obligation

import frflow.core.analysis.Resolved
import frflow.core.consistency.{Consistency, Group, Standing}
import frflow.core.name.NodeId

/** Whether the statements below a node are shown to hold together by FrFlow's witnesses: every consistency group
  * holding one of them stands witnessed. An authored `complete` on a node that is not is also asked `feasible`.
  */
object Witnessed:
  def below(r: Resolved, n: NodeId): Boolean =
    val under = descendants(r, List(n), Set.empty) - n
    Consistency.of(r.theory).collect {
      case g @ Group.Sharing(ids, _, _, _, _) if ids.exists(under) => g.standing
      case g @ Group.Premises(ids, _, _) if ids.exists(under)      => g.standing
    }
      .forall(_ == Standing.Witnessed)

  private def descendants(r: Resolved, todo: List[NodeId], seen: Set[NodeId]): Set[NodeId] = todo match
    case Nil                    => seen
    case n :: rest if seen(n)   => descendants(r, rest, seen)
    case n :: rest              => descendants(r, r.theory.refinement.parts(n) ++ rest, seen + n)
