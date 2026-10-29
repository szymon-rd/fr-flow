package frflow.core.checking

import frflow.core.analysis.Constrained
import frflow.core.code.Code
import frflow.core.expr.OutsideFact
import frflow.core.name.{DefName, NodeId}
import frflow.core.spec.NodeKind
import frflow.core.Theory

/** How the code under a node is shown to meet what is decided, piece by piece. */
final case class Shown(proven: List[DefName], tested: List[Tested], assumed: List[Assumed])

object Shown:
  /** One function of the statement, the code defining the Definitions it mentions and, of the assumption that only
    * the code changes a model's state, the operations' plain Scala, tested against the model (its runs are reported
    * there): the only place this is decided.
    */
  def of(t: Theory, id: NodeId): Shown =
    val attached = Constrained.of(t, id).flatMap(t.code.attached.get).map(_.code)
    val models = t.node(id).flatMap(_.statement.outside).collect { case OutsideFact.OnlyCodeChanges(m) => m }
      .filter(t.code.implemented.contains)
    Shown(attached.flatMap(_.proven), attached.flatMap(tested) ++ models.map(Tested.Model(_)), promised(t, id))

  private def tested(c: Code) = c match
    case Code.Tested(_, _) => List(Tested.Plain)
    case _                 => Nil

  /** An assumption about a Definition with code: an outside system's promise, its Scala tested against it. */
  private def promised(t: Theory, id: NodeId) =
    t.node(id).map(_.statement).filter(s => s.call.isDefined && s.kind == NodeKind.Assumption)
      .map(_ => Assumed.Assumption).toList
