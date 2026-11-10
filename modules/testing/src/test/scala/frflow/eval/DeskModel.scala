package frflow.eval

import frflow.*
import scala.annotation.experimental

/** The desk's statements, about its service method as a function of the table's rows (`Desk.book`). */
@experimental object DeskModel:
  import Desk.{Booking, noOverlap}

  val booked = Definition[(List[Booking], Booking) => (Boolean, List[Booking])](
    "booking a request, from the table's rows: whether it was booked, and the rows after it")

  /** Whether a request overlaps no booking of its room among the rows. */
  val roomFree = define { (rows: Term[List[Booking]], request: Term[Booking]) =>
    rows.filter(b => b.room === request.room).forall(b => noOverlap(b, request)) }

  val answersWhenFree = Node.claim("A request is answered booked exactly when it overlaps no booking of its room.")(
    forall((rows: Term[List[Booking]], request: Term[Booking]) =>
      booked(rows, request)._1 === roomFree(rows, request)))

  val storesWhenFree = Node.claim("Booking a request leaves the table holding what it held, with the request added " +
      "at the end if it overlaps no booking of its room.")(
    forall((rows: Term[List[Booking]], request: Term[Booking]) =>
      booked(rows, request)._2 === when(roomFree(rows, request))(rows :+ request).otherwise(rows)))

  val model: FrModel = FrModel("Desk")(answersWhenFree, storesWhenFree).implementProven(booked)(Desk.book)
