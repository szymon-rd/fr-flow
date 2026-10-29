package frflow.project.pipeline

import frflow.core.analysis.{Constrained, SaysWhat}
import frflow.core.name.NodeId
import frflow.core.Theory

/** Whether a statement's check includes tests of plain Scala: it mentions a Definition whose meaning is plain Scala,
  * which is tested against it on generated cases (a claim) or tested to keep it (an outside system's promise). A claim
  * saying what a Declaration is has no code checked against it (2.7).
  */
object Testable:
  def of(t: Theory, id: NodeId): Boolean =
    t.node(id).exists(_.statement.said.isDefined) && !SaysWhat.is(t, id) &&
      Constrained.of(t, id).flatMap(t.code.attached.get).exists(_.code.scala.nonEmpty)
