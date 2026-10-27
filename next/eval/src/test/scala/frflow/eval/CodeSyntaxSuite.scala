package frflow.eval

import cats.effect.{IO, Ref}
import cats.effect.unsafe.implicits.global
import frflow.*
import rooms.{BookIfGranted, Booking, BookingTable, Request, RoomBookings}

/** A program in production as the developer runs it: `knowledge.running[F]()`, its conditions evaluated over every
  * Definition's meaning (rooms' `granted`, plain Scala), its adapter plain Scala lifted (`BoundaryOps.lifted`).
  */
class CodeSyntaxSuite extends munit.FunSuite:
  /** A table in memory, plain Scala over plain values. */
  private final class Memory(held: Ref[IO, List[Booking]]) extends BookingTable[IO, cats.Id]:
    def inRoom(room: String): IO[RoomBookings] = held.get.map(bs => RoomBookings(room, bs.filter(_.room == room)))
    def add(booking: Booking): IO[Unit] = held.update(_ :+ booking)

  private def booked(requests: List[Request]): (List[Boolean], List[Booking]) = (for
    run    <- rooms.rooms.running[IO]()
    held   <- IO.ref(List(Booking("Oak", 9, 10)))
    table   = rooms.bookingTable.lifted(Memory(held), run)
    asked  <- IO.parTraverseN(1)(requests)(r => BookIfGranted[IO](table)(using run).run(run.term(r)).map(run.value))
    stored <- held.get
  yield (asked, stored)).unsafeRunSync()

  test("rooms' book in production: a free room's request booked, one that overlaps refused") {
    assertEquals(booked(List(Request("Oak", 10, 11), Request("Oak", 9, 11))),
      (List(true, false), List(Booking("Oak", 9, 10), Booking("Oak", 10, 11))))
  }

  test("a proven program is run by running it, not called: its code called from plain code has no value (Steps)") {
    val book = rooms.rooms.code(rooms.book)()
    assertEquals(intercept[NotEvaluated](book(Request("Oak", 1, 2))).error, EvalError.Steps)
  }
