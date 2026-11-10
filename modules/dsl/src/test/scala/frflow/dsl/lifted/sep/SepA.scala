package frflow.dsl.lifted.sep

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.dsl.lifted.FrSpec
import frflow.dsl.lifted.LiftSyntax.lifted
import scala.annotation.experimental

/** The spike's domain, in a file Scala checks captures and separation in: data, lifted functions over it, and a
  * port (a `caps.Mutable` class whose state is its one `var`).
  */
@experimental object SepA:
  final case class Slot(room: String, start: BigInt, end: BigInt) derives FrSpec

  val noOverlap = lifted { (a: Slot, b: Slot) => a.room != b.room || a.end <= b.start || b.end <= a.start }
  val free = lifted { (held: List[Slot], r: Slot) => held.forall(b => noOverlap(b, r)) }

  final class Table(var rows: List[Slot]) extends Mutable:
    def inRoom(room: String): List[Slot] = rows.filter(b => b.room == room)
    update def add(b: Slot): Unit = rows = rows :+ b
    update def clear(): Unit = rows = Nil

  /** A service method as an ordinary `def`: what production calls, with the types Scala checks it by. */
  def reserve(table: Table^, request: Slot): Boolean =
    val ok = free(table.inRoom(request.room), request)
    if ok then table.add(request)
    ok

  /** Production's call of it, in checked code: the table is the caller's alone. */
  def reserveBoth(first: Slot, second: Slot): List[Slot] =
    val table: Table^ = Table(Nil)
    val both = reserve(table, first) && reserve(table, second)
    if both then table.rows else Nil
