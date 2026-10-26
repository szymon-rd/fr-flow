package rooms

import frflow.*
import frflow.core.example.Gen
import frflow.core.code.Values
import frflow.core.name.NodeId
import frflow.core.ty.Ty
import frflow.eval.{Env, ScalaValue, Semantics}
import frflow.eval.run.{Broken, CallCheck, Made}
import frflow.testing.{Case, Draw, Plan, PropertyTests, Respecting, Seed, Settings}
import java.util.SplittableRandom

/** R14.1: the calendar's claims range over what the store can give (`RoomBookings`, always pairwise apart), so the
  * README's binary-search calendar is correct as stated: tested on generated cases meeting what always holds (as
  * `check` draws them), it meets each claim; drawn over every list, it does not, and nothing says it should.
  */
class CalendarSuite extends munit.FunSuite:
  private val e = rooms.elaborated.fold(es => fail(es.toString), identity)
  private val semantics = Semantics(e)

  /** Values by type, as `testing`'s derived generators will draw them: bookings that end after they start, a room's
    * overlapping or not.
    */
  private object Anything extends Draw:
    def apply[A](g: Gen[A], size: Int, random: SplittableRandom): A = (g match
      case Gen.Derived(Ty.Str)                       => room(random)
      case Gen.Derived(t) if t == LeanType[Booking].ty => booking(random)
      case Gen.Derived(t) if t == LeanType[RoomBookings].ty =>
        RoomBookings(List.fill(random.nextInt(4))(booking(random)))
      case other                                     => throw IllegalArgumentException(other.toString)
    ).asInstanceOf[A]
    private def room(r: SplittableRandom) = if r.nextBoolean() then "Oak" else "Elm"
    private def booking(r: SplittableRandom) =
      val start = BigInt(r.nextInt(8))
      Booking(room(r), start, start + r.nextInt(1, 4))

  private val respecting = Respecting(Anything, Made.of(semantics, e.theory), tries = 200)
  private val plan = Plan(Settings(500, Seed(14)), Nil)
  private def tested(kb: KnowledgeBase, draw: Draw, claim: String) =
    val k = kb.elaborated.fold(es => fail(es.toString), identity)
    PropertyTests(Semantics(k), k.theory).of(NodeId(claim), plan, draw).getOrElse(fail(s"$claim is not tested"))

  test("on what the store can give, the binary-search calendar meets the calendar's claim on 500 generated cases") {
    assertEquals(tested(rooms, respecting, "grantWhenNoOverlap").failure, None)
    val drawn = (0 until 500).map(i =>
      respecting(Gen.Derived[RoomBookings](LeanType[RoomBookings].ty), 3, Seed(14).forCase(i)))
    val shared = drawn.count(r => r.bookings.groupBy(_.room).values.exists(_.size >= 2))
    assert(shared > 50, s"$shared cases with two bookings of one room")
  }

  test("on a list the store cannot give (two of a room overlapping) it is wrong, and no case draws one") {
    val (long, short, request) = (Booking("Oak", 0, 10), Booking("Oak", 1, 2), Booking("Oak", 3, 4))
    val held = RoomBookings(List(long, short))
    assertEquals(Calendar(held).grants(request), true)
    val check = CallCheck.of(semantics, e.theory, NodeId("grantWhenNoOverlap")).getOrElse(fail("a call"))
    val impl = e.theory.code.attached.get(granted.name).flatMap(_.code.scala).map(_.impl).getOrElse(fail("code"))
    val tests = PropertyTests(semantics, e.theory)
    val reflect = (v: Any, t: Ty) => semantics.reflect(ScalaValue(v), t)
    val overlapping = Case(List(reflect(held, LeanType[RoomBookings].ty), reflect(request, LeanType[Booking].ty)),
      Values.none)
    assertEquals(tests.judged(check, impl, overlapping), Some(Broken.Post))
    val apart = Made.of(semantics, e.theory).find(_.always.value == "roomBookingsApart").getOrElse(fail("made"))
    assertEquals(apart.holds(ScalaValue(held), Env.of(Values.none)), false)
  }

  test("README step 4: a calendar that forgets the booking after the request is found by a generated case") {
    val forgets = KnowledgeBase("Rooms")(rooms.nodes*).implementProven(book)(bookIfGranted)
      .implementTested(granted)(_ => (held, request) =>
        val room = held.bookings.filter(_.room == request.room).sortBy(_.start).toVector
        val next = room.search(request)(using Ordering.by(_.start)).insertionPoint
        room.lift(next - 1).forall(_.end <= request.start))
    assertEquals(tested(forgets, respecting, "grantWhenNoOverlap").failure.map(_.broke), Some(Broken.Post))
  }
