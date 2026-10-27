package rooms

import frflow.*
import frflow.core.expr.{Expr, Exprs}

/** A helper that binds through one lambda (`x => p(x)`), nested in itself. Each use is its own binder, numbered where
  * it is interpreted, so the inner one never captures the outer.
  */
class NestedHelperSuite extends munit.FunSuite:
  private def all[A: LeanType](xs: Term[List[A]])(p: Term[A] => Term[Boolean]) = xs.forall(x => p(x))

  private val noRoomBooked = define { (rooms: Term[List[String]], bookings: Term[List[Booking]]) =>
    all(rooms)(r => all(bookings)(b => r =!= b.room)) }

  test("in the IR, the two binders are two variables, the inner body reading both") {
    val body = RoomsIr.lambda(noRoomBooked).value.body
    val bound = Exprs.all(body).collect { case Expr.Iterate(_, _, x, _, _) => x }
    assertEquals(bound.map(_.id).distinct.size, 2)
    val inner = Exprs.all(body).collect { case Expr.Iterate(_, _, _, b, _) => b }.last
    assertEquals(Exprs.all(inner).collect { case Expr.Var(x) => x.id }.toSet, bound.map(_.id).toSet)
  }

  test("both binders keep the helper's name, for the printer to tell apart") {
    val body = RoomsIr.lambda(noRoomBooked).value.body
    assertEquals(Exprs.all(body).collect { case Expr.Iterate(_, _, x, _, _) => x.hint }, List("x", "x"))
  }
