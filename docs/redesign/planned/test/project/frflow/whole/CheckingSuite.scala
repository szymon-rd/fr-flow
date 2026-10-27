package whole

import frflow.*
import frflow.core.checking.Checking
import frflow.core.name.NodeId
import frflow.project.pipeline.Texts
import rooms.{Booking, Calendar, RoomBookings, granted, isFree}

/** How a reader sees how each claim is checked (owner §15): `show` lists these beside the statement, all derived from
  * its formula, its place and what defines the Definitions it mentions; nothing of it is written beside the claim.
  */
class CheckingSuite extends munit.FunSuite:
  private val t = Whole(rooms.rooms, Nil).resolved.theory
  private def checking(n: String) = Texts.checking(t, NodeId(n))

  test("the root: proven of book's program, assumed by its callers, resting on the store's model, one run at a time") {
    assertEquals(checking("bookWhenFree"), List(
      "proven of book's program, bookIfGranted",
      "assumed by the code calling book",
      "rests on the store behaving as stored: storeModel",
      "rests on one run at a time on stored: oneAtATime",
      "rests on what each Request from outside meets: fromTheForm"))
  }

  test("the calendar's claim: tested against granted's Scala, consistent by its witness") {
    assertEquals(checking("grantWhenNoOverlap"), List(
      "tested against granted's Scala on generated cases",
      "assumed by the code calling granted",
      "consistent with grantWhenNoOverlap: witnessed, for Lean to check"))
  }

  test("what always holds: kept by every run of book, from the start; met where made, entering through the form") {
    assertEquals(checking("neverOverlap"), List(
      "kept by every run of book, from the state it starts in",
      "rests on the store behaving as stored: storeModel",
      "rests on one run at a time on stored: oneAtATime",
      "rests on the state stored starts in: startsEmpty",
      "rests on who writes stored: onlyBookingWrites",
      "rests on what each Request from outside meets: fromTheForm",
      "consistent with neverOverlap: witnessed, for Lean to check"))
    assertEquals(checking("endsAfterStart"), List(
      "met where a Booking is made (book, stored's inRoom); assumed of every Booking in Lean",
      "rests on the store behaving as stored: storeModel",
      "rests on one run at a time on stored: oneAtATime",
      "rests on the state stored starts in: startsEmpty",
      "rests on who writes stored: onlyBookingWrites",
      "rests on what each Request from outside meets: fromTheForm",
      "consistent with endsAfterStart: witnessed, for Lean to check",
      "not vacuous: some Booking meets it"))
  }

  test("an assumption about the outside says so") {
    assertEquals(checking("oneAtATime"), List("the world outside: runs on stored never interleave"))
  }

  test("what the store can give: made by its model's inRoom, resting on the model, shown to admit a value") {
    assertEquals(checking("roomBookingsApart"), List(
      "met where a RoomBookings is made (stored's inRoom); assumed of every RoomBookings in Lean",
      "rests on the store behaving as stored: storeModel",
      "not vacuous: some RoomBookings meets it"))
  }

  test("a claim the calendar's Scala cannot be judged by (it quantifies over moments) is proven from its parts") {
    assertEquals(checking("grantWhenFree").take(2), List("proven from its parts (grantWhenNoOverlap)",
      "not checked against granted's Scala: the statement has no Scala value (it quantifies over every value)"))
    assert(!Checking.unchecked(t, NodeId("grantWhenFree")))
  }

  test("R14.5: a claim about tested Scala reading as no call is tested whole; one with no Scala value, not checked") {
    val whole = Node.claim("A request granted is granted again with its own room's bookings only.")(
      forall((held: Term[RoomBookings], request: Term[Booking]) => granted(held, request) implies
        granted(make[RoomBookings](held.bookings.filter(b => b.room === request.room)), request)))
    val moments = Node.claim("A request granted covers no moment a booking covers.")(
      forall((held: Term[RoomBookings], request: Term[Booking]) => granted(held, request) implies
        isFree(held.bookings, request)))
    val kb = KnowledgeBase("Rooms")(whole, moments).implementTested(granted)(_ => (h, r) => Calendar(h).grants(r))
    val u = Whole(kb, Nil).resolved.theory
    assertEquals(List("whole", "moments").map(n => Texts.checking(u, NodeId(n)).head), List(
      "tested against granted's Scala on generated cases, the statement evaluated whole",
      "not checked against granted's Scala: the statement has no Scala value (it quantifies over every value)"))
    assertEquals(List("whole", "moments").map(n => Checking.unchecked(u, NodeId(n))), List(false, true))
  }
