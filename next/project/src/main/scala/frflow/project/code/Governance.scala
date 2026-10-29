package frflow.project.code

import frflow.core.analysis.Constrained
import frflow.core.analysis.outside.Outsides
import frflow.core.checking.Checking
import frflow.core.name.{NodeId, RelPath, SymbolName}
import frflow.core.spec.Statement
import frflow.core.Theory

/** The files each node governs, today's set exactly. */
object Governance:
  def of(t: Theory, files: List[RelPath]): Map[NodeId, List[RelPath]] =
    val designs = t.nodes.flatMap(s => declared(s.node.statement).map(s.node.id -> _))
    val modelFiles = t.nodes.map(_.at.file).toSet ++ t.code.attached.values.map(_.writtenIn)
    val implied = (attachedFiles(t) ++ implementedFiles(t))
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

  /** A Definition's plain code's files, governed by each statement its code is tested against: a statement the code
    * cannot be judged by (it has no Scala value) does not rest on it.
    */
  private def attachedFiles(t: Theory): List[(NodeId, RelPath)] =
    t.code.attached.toList.flatMap((d, a) => a.code.scala.toList.flatMap(_.files)
      .flatMap(f => Constrained.statements(t, d).filter(tested(t, d, _)).map(_ -> f)))

  private def tested(t: Theory, d: SymbolName, n: NodeId): Boolean = Checking.of(t, n).exists {
    case Checking.TestedAgainst(`d`, _) => true
    case _                              => false
  }

  /** A model's operations' plain Scala's files, governed by the assumption that only the code changes its state
    * (what its model tests are reported under).
    */
  private def implementedFiles(t: Theory): List[(NodeId, RelPath)] =
    t.code.implemented.toList.flatMap((m, i) =>
      Outsides.onlyCodeChanges(t, m).toList.flatMap(n => i.files.map(n -> _)))
