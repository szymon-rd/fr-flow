package frflow.eval

import cats.effect.IO
import cats.effect.unsafe.implicits.global
import frflow.*
import rooms.{BookIfGranted, Booking, BookingsTable, storedBookings}

/** A program in production as the developer runs it: `knowledge.running[F](storedBookings := table)`, its conditions
  * evaluated over every Definition's meaning (rooms' `granted`, plain Scala), its operations' Scala bound (the SQLite
  * table, in memory).
  */
class CodeSyntaxSuite extends munit.FunSuite:
  private def booked(requests: List[Booking]): (List[Boolean], List[Booking]) = (for
    table  <- BookingsTable.holding(List(Booking("Oak", 9, 10)))
    run    <- rooms.rooms.running[IO](storedBookings := table)
    asked  <- IO.parTraverseN(1)(requests)(r => BookIfGranted.run[IO](run.term(r))(using run).map(run.value))
    stored <- table.bookings
  yield (asked, stored)).unsafeRunSync()

  test("rooms' book in production: a free room's request booked, one that overlaps refused") {
    assertEquals(booked(List(Booking("Oak", 10, 11), Booking("Oak", 9, 11))),
      (List(true, false), List(Booking("Oak", 9, 10), Booking("Oak", 10, 11))))
  }

  test("a proven program is run by running it, not called: its code called from plain code has no value (Steps)") {
    val book = rooms.rooms.code(rooms.book)()
    assertEquals(intercept[NotEvaluated](book(Booking("Oak", 1, 2))).error, EvalError.Steps)
  }
