package frflow.dsl.build

import cats.syntax.all.*
import frflow.core.name.RelPath

/** Where a Definition is written: its file (none: FrFlow's own, the clock's), and, of a program, the definitions its
  * body refers to, by file (`SourceFiles`: `program { Delivery.run }` refers to `Delivery` and its `run`).
  */
final case class WrittenAt(file: Option[RelPath], refers: List[(RelPath, List[String])]):
  /** That the Definition `name` is written here, and its body refers to what it does. */
  def declares(name: String): Declarations = Declarations.in(file, name) |+| Declarations.refers(refers)

object WrittenAt:
  val none: WrittenAt = WrittenAt(None, Nil)
  def in(file: RelPath): WrittenAt = WrittenAt(Some(file), Nil)
