package frflow.dsl.lifted

import frflow.core.expr.Lambda
import frflow.dsl.lifted.LiftSyntax.lifted
import frflow.dsl.shape.Defines.define
import frflow.dsl.term.Term
import frflow.dsl.term.TermSyntax.*
import frflow.dsl.vocab.Definition

/** Plain Scala read by `lifted` is the term a model writes with the DSL: the two have one IR, binder for binder
  * (the names aside: a define's is its val's), so Lean prints one `def` for both and the evaluator runs both alike.
  */
class LiftedSuite extends munit.FunSuite:
  private def lambda(d: Definition[?]): Lambda =
    d.onTheSpot.fold(fail(s"${d.name} has no meaning where it is written"))(_.lambda.run.fold(
      es => fail(es.toChain.toList.mkString("; ")), _._2.value))

  private def same(read: Definition[?], written: Definition[?]): Unit =
    assertEquals(lambda(read), lambda(written))

  private val noOverlap = lifted { (a: Booking, b: Booking) =>
    a.room != b.room || a.end <= b.start || b.end <= a.start }
  private val noOverlapWritten = define { (a: Term[Booking], b: Term[Booking]) =>
    a.room =!= b.room || a.end <= b.start || b.end <= a.start }

  test("fields, comparisons, equality and the connectives") {
    same(noOverlap, noOverlapWritten)
  }

  private val granted = lifted { (held: RoomBookings, request: Booking) =>
    held.bookings.forall(b => noOverlap(b, request)) }
  private val grantedWritten = define { (held: Term[RoomBookings], request: Term[Booking]) =>
    held.bookings.forall(b => noOverlap(b, request)) }

  test("a list's forall over a lambda, and a call of another lifted function by name") {
    same(granted, grantedWritten)
  }

  private val added = lifted { (bookings: List[Booking], request: Booking) =>
    if bookings.forall(b => noOverlap(b, request)) then bookings :+ request else bookings }
  private val addedWritten = define { (bookings: Term[List[Booking]], request: Term[Booking]) =>
    when(bookings.forall(b => noOverlap(b, request)))(bookings :+ request).otherwise(bookings) }

  test("a conditional, and a list with an element added") {
    same(added, addedWritten)
  }

  private val length = lifted { (b: Booking) =>
    val span = b.end - b.start
    if span < BigInt(0) then BigInt(0) else span }
  private val lengthWritten = define { (b: Term[Booking]) =>
    let(b.end - b.start)(span => when(span < 0)(0: Term[BigInt]).otherwise(span)) }

  test("a value named, and numbers") {
    same(length, lengthWritten)
  }

  private val area = lifted { (s: Shape) =>
    s match
      case Shape.Circle(r)  => r + r + r
      case Shape.Rect(w, h) => w + h
      case Shape.Empty      => BigInt(0) }
  private val areaWritten = define { (s: Term[Shape]) =>
    s.on[Shape.Circle](r => r + r + r).on[Shape.Rect]((w, h) => w + h).on[Shape.Empty.type](0: Term[BigInt]) }

  test("a match on an enum, each case's fields bound") {
    same(area, areaWritten)
  }

  private val isEmpty = lifted { (s: Shape) =>
    s match
      case Shape.Empty => true
      case _           => false }
  private val isEmptyWritten = define { (s: Term[Shape]) =>
    s.on[Shape.Circle](_ => False).on[Shape.Rect]((_, _) => False).on[Shape.Empty.type](True) }

  test("a match's default stands for every case not written, in the enum's order") {
    same(isEmpty, isEmptyWritten)
  }

  private val firstIn = lifted { (bookings: List[Booking], room: String) =>
    bookings.find(b => b.room == room) match
      case Some(b) => b.start
      case None    => BigInt(0) }
  private val firstInWritten = define { (bookings: Term[List[Booking]], room: Term[String]) =>
    bookings.find(b => b.room === room).fold(0: Term[BigInt])(b => b.start) }

  test("a list's find and a match on the option it gives") {
    same(firstIn, firstInWritten)
  }

  private val moved = lifted { (b: Booking, by: BigInt) => b.copy(start = b.start + by, end = b.end + by) }
  private val movedWritten = define { (b: Term[Booking], by: Term[BigInt]) =>
    b.updated(_.start, b.start + by).updated(_.end, b.end + by) }

  test("a copy with fields replaced") {
    same(moved, movedWritten)
  }

  private val whole = lifted { (room: String, from: BigInt) => Booking(room, from, from + BigInt(1)) }
  private val wholeWritten = define { (room: Term[String], from: Term[BigInt]) =>
    make[Booking](room, from, from + 1) }

  test("a case class's value made from its fields") {
    same(whole, wholeWritten)
  }

  private val covered = lifted { (b: Booking, t: BigInt) => b.covers(t) }
  private val coveredWritten = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }

  test("an inline method's body is read where it is called") {
    same(covered, coveredWritten)
  }

  private val starts = lifted { (held: RoomBookings) =>
    held.bookings.filter(b => b.room == held.room).map(b => b.start).foldLeft(BigInt(0))((sum, s) => sum + s) }
  private val startsWritten = define { (held: Term[RoomBookings]) =>
    held.bookings.filter(b => b.room === held.room).map(b => b.start).foldLeft(0: Term[BigInt])((sum, s) =>
      sum + s) }

  test("filter, map and foldLeft") {
    same(starts, startsWritten)
  }

  test("lifted code is the Scala it is written as") {
    val (nine, ten) = (Booking("Oak", 9, 10), Booking("Oak", 10, 11))
    assert(noOverlap(nine, ten))
    assert(!noOverlap(nine, Booking("Oak", 9, 11)))
    assert(granted(RoomBookings("Oak", List(nine)), ten))
    assertEquals(area(Shape.Rect(2, 3)), BigInt(5))
    assertEquals(moved(nine, 1), Booking("Oak", 10, 11))
  }
