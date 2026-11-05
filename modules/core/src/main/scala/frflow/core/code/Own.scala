package frflow.core.code

import cats.syntax.all.*
import frflow.core.name.RelPath

/** What of the model is written where, beside its nodes: the names of its vocabulary (Declarations, Definitions,
  * defines, programs, models of a state, domain types), by the file each is written in; and the definitions its
  * programs' bodies refer to (a plain `def` building a program's steps), by file. A file holding only these is the
  * model's own (`project.code.ModelFiles`).
  */
final case class Own(vocabulary: Map[RelPath, Set[String]], referred: Map[RelPath, Set[String]]):
  def moved(move: RelPath => RelPath): Own =
    Own(Own.moved(vocabulary, move), Own.moved(referred, move))

object Own:
  val none: Own = Own(Map.empty, Map.empty)

  private def moved(m: Map[RelPath, Set[String]], move: RelPath => RelPath): Map[RelPath, Set[String]] =
    m.toList.map((f, ns) => Map(move(f) -> ns)).combineAll
