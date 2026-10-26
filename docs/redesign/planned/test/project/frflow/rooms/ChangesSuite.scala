package rooms

import frflow.*
import frflow.core.code.Values
import frflow.core.expr.{Expr, Exprs, Pattern}

/** R8.2: matching an enum, a record made and updated, the folds and `let` (`Changes.scala`), each printed as Lean from
  * its term, run by the evaluator, and read by the analyses as IR, with no cast anywhere.
  */
class ChangesSuite extends munit.FunSuite:
  import RoomsLean.{define, elaborated}
  private def lean(d: Definition[?]): String = define(elaborated(RoomsLean.lambda(d)))
  private val (oak, elm) = (Booking("Oak", 9, 10), Booking("Elm", 1, 3))

  test("a match over an enum prints one arm per case, each case's fields named by the developer's names") {
    assertEquals(lean(afterChange), "(held : (List Booking)) (c : Change) := (match c with " +
      "| Change.Book b => (b :: held) " +
      "| Change.Cancel room start => " +
      "(List.filter (fun b => decide (¬((b.room = room) ∧ (b.start = start)))) held) " +
      "| Change.Clear => [])")
  }

  test("a match runs the arm of the value's case, on its fields") {
    val after = afterChange.fn(Values.none)
    assertEquals((after(List(elm), Change.Book(oak)), after(List(oak, elm), Change.Cancel("Oak", 9)),
      after(List(oak), Change.Clear)), (List(oak, elm), List(elm), Nil))
  }

  test("in the IR, a match binds each case's fields as its pattern's variables") {
    val body = elaborated(RoomsLean.lambda(afterChange)).value.body
    val patterns = Exprs.all(body).collect { case Expr.Match(_, arms, _) => arms.map(_.pattern) }.flatten
    assertEquals(patterns.map { case Pattern.Ctor(_, c, xs) => c.value -> xs.map(_.hint); case p => p.toString -> Nil },
      List("Book" -> List("b"), "Cancel" -> List("room", "start"), "Clear" -> Nil))
  }

  test("a record updated, a fold, a record made and shared by `let`, an option's and an either's fold, as Lean") {
    assertEquals(List(moved, booked, hourLong, startOr).map(lean), List(
      "(b : Booking) (t : Int) := { { b with start := t } with «end» := (t + (b.«end» - b.start)) }",
      "(held : (List Booking)) := (List.foldl (fun (n : Int) (b : Booking) => (n + (b.«end» - b.start))) 0 held)",
      "(room : String) (t : Int) := (let b : Booking := (Booking.mk room t (t + 1)); (b.«end» - b.start))",
      "(o : (Option Booking)) (t : Int) := (match o with | none => t | some b => b.start)"))
  }

  test("the same, run") {
    assertEquals((moved.fn(Values.none)(oak, 12), booked.fn(Values.none)(List(oak, elm)),
      hourLong.fn(Values.none)("Oak", 4), startOr.fn(Values.none)(None, 7), startOr.fn(Values.none)(Some(elm), 7),
      outcome.fn(Values.none)(Left("no"), 5), outcome.fn(Values.none)(Right(oak), 5)),
      (Booking("Oak", 12, 13), BigInt(3), BigInt(1), BigInt(7), BigInt(1), BigInt(5), BigInt(10)))
  }
