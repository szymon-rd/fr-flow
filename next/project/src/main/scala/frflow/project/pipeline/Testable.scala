package frflow.project.pipeline

import frflow.core.analysis.Constrained
import frflow.core.name.NodeId
import frflow.core.Theory

/** Whether a statement's check includes tests of plain Scala: it mentions a Definition whose meaning is plain Scala,
  * which is tested against it on generated cases (a claim) or tested to keep it (an outside system's promise).
  */
object Testable:
  def of(t: Theory, id: NodeId): Boolean =
    t.node(id).exists(_.statement.said.isDefined) &&
      Constrained.of(t, id).flatMap(t.code.attached.get).exists(_.code.scala.nonEmpty)
