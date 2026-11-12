package frflow.project.pipeline

import frflow.core.analysis.resolution.{Constrained, Resolved}
import frflow.core.code.Code
import frflow.core.name.NodeId
import frflow.core.Theory
import frflow.wire.snapshot.Rows

/** The content field of the code: what gives each Definition a statement mentions its meaning. */
object CodeTexts:
  /** One line per Definition it mentions that has a meaning, sorted: the define's source, the plain Scala's
    * expression, the value fixed, or that it is provided where the code runs.
    */
  def implementation(r: Resolved, id: NodeId): Option[String] =
    val t = r.theory
    Option(Constrained.of(t, id).sortBy(_.value).flatMap(s => t.code.attached.get(s).map(a =>
      s"${s.value}: ${coded(t, a.code)}"))).filter(_.nonEmpty).map(_.mkString("\n"))

  private def coded(t: Theory, c: Code): String = c match
    case Code.Proven(d)       => s"proven, ${t.vocabulary.define(d).fold(d.value)(_.written.source.value)}"
    case Code.Tested(runs, _) => s"Scala, ${runs.written.value}"
    case Code.Valued(v)       => s"the value ${Rows.shown(v)}"
    case Code.Provided        => "provided where the code runs"
