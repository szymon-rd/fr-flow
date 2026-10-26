package rooms

import cats.syntax.all.*

class RoomsSuite extends munit.CatsEffectSuite:
  test("booking on SQLite: a request overlapping a booking of its room is not booked, one in another room is") {
    val sql = SqliteBookings.open(":memory:")
    for
      first   <- bookOn(sql)(Booking("Oak", 9, 11))
      overlap <- bookOn(sql)(Booking("Oak", 10, 12))
      elm     <- bookOn(sql)(Booking("Elm", 10, 12))
    yield
      assertEquals((first, overlap, elm), (true, false, true))
      assertEquals(sql.held, List(Booking("Oak", 9, 11), Booking("Elm", 10, 12)))
  }

  test("twenty requests at once for the same time: one is booked") {
    val sql = SqliteBookings.open(":memory:")
    List.fill(20)(Booking("Oak", 9, 11)).parTraverse(bookOn(sql)).map { booked =>
      assertEquals(booked.count(identity), 1)
      assertEquals(sql.held, List(Booking("Oak", 9, 11)))
    }
  }
