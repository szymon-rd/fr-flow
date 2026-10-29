package frflow.project.code

import frflow.core.analysis.Constrained
import frflow.core.analysis.outside.Outsides
import frflow.core.checking.Checking
import frflow.core.code.CodeFile
import frflow.core.name.{ModelName, NodeId, RelPath, SymbolName}
import frflow.core.spec.Statement
import frflow.core.Theory

/** The code each node governs: each design's files, whole; and the files of the plain Scala each statement is tested
  * against, whole, but in a file that holds nodes (or the FrModel), only the definitions the Scala refers to (owner
  * §38).
  */
object Governance:
  def of(t: Theory, files: List[RelPath]): Map[NodeId, List[Governed]] =
    val designs = t.nodes.flatMap(s => declared(s.node.statement).map(s.node.id -> _))
    val implied = (attachedFiles(t) ++ implementedFiles(t))
      .filterNot((_, f) => designs.exists((_, g) => f.path.isUnder(g)))
      .flatMap((n, f) => governed(t, f).map(n -> _))
    (designs.flatMap((n, g) => under(g, files).map(n -> Governed.Whole(_))) ++ implied).groupMap(_._1)(_._2)
      .view.mapValues(gs => merged(gs.distinct)).toMap

  /** What of a file plain Scala refers to is governed: in a file that holds nodes, the definitions it names (none:
    * nothing); any other file whole.
    */
  def governed(t: Theory, f: CodeFile): Option[Governed] =
    val beside = t.nodes.map(_.at.file).toSet ++ t.code.attached.values.map(_.writtenIn)
    if !beside(f.path) then Some(Governed.Whole(f.path))
    else Option.when(f.names.nonEmpty)(Governed.Named(f.path, f.names))

  /** One per file, by path: a file governed whole wins over its definitions. */
  private def merged(gs: List[Governed]): List[Governed] = gs.groupBy(_.path).toList.sortBy(_._1).map((p, same) =>
    if same.exists { case Governed.Whole(_) => true; case _ => false } then Governed.Whole(p)
    else Governed.Named(p, same.flatMap { case Governed.Named(_, ns) => ns; case _ => Nil }.distinct.sorted))

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
  private def attachedFiles(t: Theory): List[(NodeId, CodeFile)] =
    t.code.attached.toList.flatMap((d, a) => a.code.scala.toList.flatMap(_.files)
      .flatMap(f => Constrained.statements(t, d).filter(tested(t, d, _)).map(_ -> f)))

  private def tested(t: Theory, d: SymbolName, n: NodeId): Boolean = Checking.of(t, n).exists {
    case Checking.TestedAgainst(`d`, _) => true
    case _                              => false
  }

  /** A model's operations' plain Scala's files, governed by the assumption that only the code changes its state, or,
    * with none, by each statement resting on that Scala (`TestedOnModel`).
    */
  private def implementedFiles(t: Theory): List[(NodeId, CodeFile)] =
    t.code.implemented.toList.flatMap((m, i) =>
      Outsides.onlyCodeChanges(t, m).fold(resting(t, m))(List(_)).flatMap(n => i.files.map(n -> _)))

  private def resting(t: Theory, m: ModelName): List[NodeId] = t.nodes.map(_.node.id).filter(n =>
    Checking.of(t, n).exists { case Checking.TestedOnModel(`m`, _) => true; case _ => false })
