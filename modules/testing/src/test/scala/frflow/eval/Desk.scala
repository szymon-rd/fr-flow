package frflow.eval

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import scala.annotation.experimental
import frflow.*
import frflow.dsl.lifted.steps.StepSyntax.updating

/** A booking desk whose service method is direct-style Scala over a port (a spike): the table is a class of Scala's
  * `caps.Mutable`, the method has it to itself (`Table^`, which separation checking checks), and FrFlow reads the
  * method into a function of the table's rows that gives its answer with the rows after it. Capture and separation
  * checking are experimental in Scala, so what is written with them is marked so, and so is what uses it.
  */
@experimental object Desk:
  final case class Booking(room: String, start: BigInt, end: BigInt) derives FrSpec

  /** The bookings table, a port: its state is its rows; reading is an ordinary method, changing an `update`. */
  final class Table(var rows: List[Booking]) extends Mutable:
    def inRoom(room: String): List[Booking] = rows.filter(b => b.room == room)
    update def add(b: Booking): Unit = rows = rows :+ b

  val noOverlap = lifted { (a: Booking, b: Booking) => a.room != b.room || a.end <= b.start || b.end <= a.start }

  val free = lifted { (held: List[Booking], request: Booking) => held.forall(b => noOverlap(b, request)) }

  /** The service method: the room's bookings read, the request added when it overlaps none of them. */
  val book = updating { (table: Table^, request: Booking) =>
    val held = table.inRoom(request.room)
    val ok = free(held, request)
    if ok then table.add(request)
    ok }
