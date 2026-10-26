package rooms

import frflow.*
import frflow.core.code.Values
import frflow.core.expr.{Expr, Exprs}

/** R7.2: a helper that binds through one lambda (`x => p(x)`), nested in itself. Each use is its own binder, named
  * and numbered where it is interpreted, so the inner one never captures the outer.
  */
class NestedHelperSuite extends munit.FunSuite:
  private def all[A: LeanType](xs: Term[List[A]])(p: Term[A] => Term[Boolean]) = xs.forall(x => p(x))

  private val noRoomBooked = define { (rooms: Term[List[String]], bookings: Term[List[Booking]]) =>
    all(rooms)(r => all(bookings)(b => r =!= b.room)) }

  test("printed, the two binders have two names, and the inner body names the outer one") {
    assertEquals(RoomsLean.define(RoomsLean.elaborated(RoomsLean.lambda(noRoomBooked))),
      "(rooms : (List String)) (bookings : (List Booking)) := " +
      "(∀ x ∈ rooms, (∀ x_1 ∈ bookings, (¬(x = x_1.room))))")
  }

  test("in the IR, the two binders are two variables") {
    val body = RoomsLean.elaborated(RoomsLean.lambda(noRoomBooked)).value.body
    val bound = Exprs.all(body).collect { case Expr.Iterate(_, _, x, _, _) => x.id }
    assertEquals(bound.distinct.size, 2)
  }

  test("run, a room no booking names is told apart from one a booking names") {
    val run = noRoomBooked.fn(Values.none)
    assertEquals((run(List("Elm"), List(Booking("Oak", 1, 2))), run(List("Oak"), List(Booking("Oak", 1, 2)))),
      (true, false))
  }
