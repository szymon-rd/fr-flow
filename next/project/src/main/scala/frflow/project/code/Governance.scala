package frflow.project.code

import frflow.core.analysis.Constrained
import frflow.core.analysis.Outsides
import frflow.core.name.{NodeId, RelPath}
import frflow.core.spec.Statement
import frflow.core.Theory

/** The files each node governs, today's set exactly. */
object Governance:
  def of(t: Theory, files: List[RelPath]): Map[NodeId, List[RelPath]] =
    val designs = t.nodes.flatMap(s => declared(s.node.statement).map(s.node.id -> _))
    val modelFiles = t.nodes.map(_.at.file).toSet ++ t.code.attached.values.map(_.writtenIn)
    val implied = (attachedFiles(t) ++ realizedFiles(t))
      .filterNot((_, f) => modelFiles(f) || designs.exists((_, g) => f.isUnder(g)))
    (designs.flatMap((n, g) => under(g, files).map(n -> _)) ++ implied).groupMap(_._1)(_._2)
      .view.mapValues(_.distinct.sorted).toMap

  /** A design's path: the files under it, or the path itself (missing, or a file not among the sources). */
  private def under(g: RelPath, files: List[RelPath]): List[RelPath] = files.filter(_.isUnder(g)) match
    case Nil   => List(g)
    case found => found

  private def declared(s: Statement): List[RelPath] = s match
    case Statement.Design(gs) => gs.toList
    case _                    => Nil

  /** A Definition's plain code's files, governed by every statement mentioning it. */
  private def attachedFiles(t: Theory): List[(NodeId, RelPath)] =
    t.code.attached.toList.flatMap((d, a) => a.code.scala.toList.flatMap(_.files)
      .flatMap(f => Constrained.statements(t, d).map(_ -> f)))

  /** A store's implementations' files, governed by the assumption that it behaves as its model. */
  private def realizedFiles(t: Theory): List[(NodeId, RelPath)] =
    t.code.realized.toList.flatMap((b, rs) => rs.toList.flatMap(_.runs.files).flatMap(f =>
      Outsides.modelled(t, b).map(_ -> f)))
