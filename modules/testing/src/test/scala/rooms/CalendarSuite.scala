package rooms

import frflow.*
import frflow.core.code.Values
import frflow.core.example.Gen
import frflow.core.name.NodeId
import frflow.core.ty.Ty
import frflow.eval.{Env, ScalaValue, Semantics}
import frflow.eval.run.{Broken, CallCheck, Made}
import frflow.testing.{Case, Plan, PropertyTests, Seed, Settings}
import frflow.testing.derive.Derive
import frflow.testing.report.Failure

/** R14.1: the calendar's claims range over what the store can give (`RoomBookings`, always of one room and apart), so
  * the README's binary-search calendar is correct as stated: tested on generated cases meeting what always holds (as
  * `check` draws them, by the derived generators), it meets each claim; on a list the store cannot give, it does
  * not, and nothing says it should.
  */
class CalendarSuite extends munit.FunSuite:
  private val e = rooms.elaborated.fold(es => fail(es.toString), identity)
  private val semantics = Semantics(e)
  private val draw = Derive.of(e, Nil)
  private val plan = Plan(Settings(500, Seed(14)), Nil)
  private def tested(kb: FrModel, claim: String) =
    val k = kb.elaborated.fold(es => fail(es.toString), identity)
    PropertyTests(Semantics(k), k.theory).of(NodeId(claim), plan, Derive.of(k, Nil))
      .getOrElse(fail(s"$claim is not tested"))

  test("on what the store can give, the binary-search calendar meets the calendar's claim on 500 generated cases") {
    val report = tested(rooms, "grantWhenNoOverlap")
    assertEquals((report.failure, report.cases), (None, 500))
    val drawn = (0 until 500).flatMap(i => draw(Gen.Derived[RoomBookings](LeanType[RoomBookings].ty), 3,
      Seed(14).forCase(i)))
    val shared = drawn.count(_.bookings.size >= 2)
    assert(shared > 50, s"$shared cases with two bookings of one room")
  }

  test("on a list the store cannot give (two of a room overlapping) it is wrong, and no case draws one") {
    val (long, short, request) = (Booking("Oak", 0, 10), Booking("Oak", 1, 2), Booking("Oak", 3, 4))
    val held = RoomBookings("Oak", List(long, short))
    assertEquals(Calendar(held).grants(request), true)
    val check = CallCheck.of(semantics, e.theory, NodeId("grantWhenNoOverlap")).getOrElse(fail("a call"))
    val impl = e.theory.code.attached.get(granted.name).flatMap(_.code.scala).map(_.impl).getOrElse(fail("code"))
    val tests = PropertyTests(semantics, e.theory)
    val reflect = (v: Any, t: Ty) => semantics.reflect(ScalaValue(v), t)
    val overlapping = Case(List(reflect(held, LeanType[RoomBookings].ty), reflect(request, LeanType[Booking].ty)), Nil)
    assertEquals(tests.judged(check, impl, overlapping), Some(Broken.Post))
    val apart = Made.of(semantics, e.theory).find(_.always.value == "roomBookingsApart").getOrElse(fail("made"))
    assertEquals(apart.holds(ScalaValue(held), Env.of(Values.none)), false)
  }

  test("README step 4: a calendar that forgets the booking after the request is found by a generated case") {
    val forgets = FrModel("Rooms")(rooms.nodes*).copy(generators = rooms.generators)
      .implementProven(book)(bookIfGranted)
      .implementTested(granted)(_ => (held, request) =>
        val room = held.bookings.sortBy(_.start).toVector
        val next = room.search(request)(using Ordering.by(_.start)).insertionPoint
        request.room != held.room || room.lift(next - 1).forall(_.end <= request.start))
    assertEquals(tested(forgets, "grantWhenNoOverlap").failure.collect { case Failure.Call(_, _, b, _) => b },
      Some(Broken.Post))
  }

  test("a value the code makes breaking what always holds of its type is found: the booking it moves a request to") {
    val moved = Definition[Booking => Booking]("the booking a request is moved to")
    val sameRoom = Node.claim("A request is moved within its room.")(
      forall((r: Term[Booking]) => moved(r).room === r.room))
    val endFirst = FrModel("Rooms")((rooms.nodes :+ sameRoom)*).implementProven(book)(bookIfGranted)
      .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))
      .implementTested(moved)(_ => r => Booking(r.room, r.end, r.start))
    assertEquals(tested(endFirst, "sameRoom").failure.collect { case Failure.Call(_, _, b, _) => b },
      Some(Broken.Always(NodeId("bookingsEndAfterStart"))))
  }
