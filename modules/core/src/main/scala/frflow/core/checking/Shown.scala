package frflow.core.checking

import frflow.core.analysis.resolution.Constrained
import frflow.core.name.{DefName, NodeId}
import frflow.core.spec.NodeKind
import frflow.core.Theory

/** How the code under a node is shown to meet what is decided: the defines proven, whether plain Scala is tested
  * against it, and whether it is an outside system's promise (an assumption about a Definition with code, its Scala
  * tested against it).
  */
final case class Shown(proven: List[DefName], tested: Boolean, assumed: Boolean)

object Shown:
  /** One function of the statement and the code defining the Definitions it mentions: the only place this is
    * decided.
    */
  def of(t: Theory, id: NodeId): Shown =
    val attached = Constrained.of(t, id).flatMap(t.code.attached.get).map(_.code)
    val promised = t.node(id).map(_.statement).exists(s => s.call.isDefined && s.kind == NodeKind.Assumption)
    Shown(attached.flatMap(_.proven), attached.exists(_.scala.nonEmpty), promised)
