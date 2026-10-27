package frflow.core.checking

import frflow.core.analysis.Constrained
import frflow.core.code.{Code, Realizes}
import frflow.core.expr.OutsideFact
import frflow.core.name.{DefName, NodeId}
import frflow.core.spec.NodeKind
import frflow.core.Theory

/** How the code under a node is shown to meet what is decided, piece by piece. */
final case class Shown(proven: List[DefName], tested: List[Tested], assumed: List[Assumed])

object Shown:
  /** One function of the statement, the code defining the Definitions it mentions and the implementations of the
    * store it says behaves as its model: the only place this is decided.
    */
  def of(t: Theory, id: NodeId): Shown =
    val attached = Constrained.of(t, id).flatMap(t.code.attached.get).map(_.code)
    val stores = t.node(id).flatMap(_.statement.outside).collect { case OutsideFact.BehavesAs(b, _) => b }
    val realized = stores.toList.flatMap(t.code.realized.get).flatMap(_.toList).zipWithIndex
    Shown(attached.flatMap(_.proven),
      attached.flatMap(tested) ++ realized.collect { case (r, i) if r.how == Realizes.Own => Tested.Own(i) },
      promised(t, id) ++ realized.collect { case (r, i) if r.how == Realizes.Outside => Assumed.Outside(i) })

  private def tested(c: Code) = c match
    case Code.Tested(_, _) => List(Tested.Plain)
    case _                 => Nil

  /** An assumption about a Definition with code: an outside system's promise, its adapter tested against it. */
  private def promised(t: Theory, id: NodeId) =
    t.node(id).map(_.statement).filter(s => s.call.isDefined && s.kind == NodeKind.Assumption)
      .map(_ => Assumed.Assumption).toList
