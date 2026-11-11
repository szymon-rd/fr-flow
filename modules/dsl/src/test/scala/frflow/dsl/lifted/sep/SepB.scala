package frflow.dsl.lifted.sep

import language.experimental.captureChecking
import language.experimental.separationChecking
import frflow.dsl.lifted.steps.StepSyntax.{interleaving, updating}
import scala.annotation.experimental
import scala.compiletime.testing.typeCheckErrors

/** Service methods in direct style over a port they have to themselves, read by `updating`; and what Scala's
  * separation checking refuses of such code, which the reader's state passing rests on.
  */
@experimental object SepB:
  import SepA.{Desk, Halls, Nameless, Slot, Table, free, reserve}

  val book = updating { (table: Table^, request: Slot) =>
    val held = table.inRoom(request.room)
    val ok = free(held, request)
    if ok then table.add(request)
    ok }

  /** Two changes in sequence, the second reading what the first left. */
  val replace = updating { (table: Table^, only: Slot) =>
    table.clear()
    table.add(only)
    table.inRoom(only.room).contains(only) }

  /** A service method that is an ordinary `def`, read where it is named: the `def` stays what production calls. */
  val reserved = updating { (table: Table^, request: Slot) => reserve(table, request) }

  /** A service's method, alone and among other calls. */
  val take = updating { (desk: Desk^, request: Slot) => desk.take(request) }
  val takeAmongOthers = interleaving { (desk: Desk^, request: Slot) => desk.take(request) }(SepA.others)

  /** A service over two ports: each call changes the part of the state that is its port's. */
  val move = updating { (halls: Halls^, s: Slot) => halls.move(s) }

  /** What the reader does not read of Scala that changes a port. */
  val nameless: List[String] = typeCheckErrors(
    "updating { (both: Nameless^, s: Slot) => both.add(s) }").map(_.message)

  val inLambda: List[String] = typeCheckErrors(
    "updating { (table: Table^, request: Slot) => List(request).map(s => table.add(s)).isEmpty }").map(_.message)
