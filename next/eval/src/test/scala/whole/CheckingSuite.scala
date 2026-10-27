package whole

import frflow.*
import frflow.core.analysis.Premise
import frflow.core.checking.Checking
import frflow.core.code.Code
import frflow.core.consistency.Standing
import frflow.core.name.{DefName, ModelName, NodeId, OpName, SymbolName, TypeName}
import frflow.core.ty.Ty
import rooms.{Booking, Calendar, RoomBookings, free, granted}

/** How each of rooms' claims is checked (owner §15): `show` lists these beside the statement, all derived from its
  * formula, its place and what defines the Definitions it mentions; nothing of it is written beside the claim. (The
  * lines `show` prints from them are `next-project`'s.)
  */
class CheckingSuite extends munit.FunSuite:
  private val t = Theories.resolved(rooms.rooms).theory
  private def checking(n: String): List[Checking] = Checking.of(t, NodeId(n))
  private val (book, held) = (SymbolName("book"), ModelName("storedBookings"))

  test("the root: proven of book's program, assumed by its callers, resting on the table's model, one run at a " +
    "time, and on what the booking form sends") {
    assertEquals(checking("bookWhenFree"), List(
      Checking.AgainstCode(book, Code.ProvenFlow(DefName("bookIfGranted"))),
      Checking.AssumedByCallers(List(book)),
      Checking.RestsOn(Premise.BehavesAs(held), Some(NodeId("tableMatchesModel"))),
      Checking.RestsOn(Premise.OneRunAtATime(held), Some(NodeId("oneAtATime"))),
      Checking.RestsOn(Premise.FromOutside(Ty.Data(TypeName("Request"))), Some(NodeId("requestsEndAfterStart")))))
  }

  test("the calendar's claim: tested against granted's Scala, call by call, consistent by its witness") {
    assertEquals(checking("grantWhenNoOverlap"), List(
      Checking.TestedAgainst(SymbolName("granted"), whole = false),
      Checking.AssumedByCallers(List(SymbolName("granted"))),
      Checking.Consistent(List(NodeId("grantWhenNoOverlap")), Standing.Witnessed)))
  }

  test("what always holds: kept by every run of book, from the start, resting on the four facts about the table") {
    assertEquals(checking("neverOverlap").take(5), List(
      Checking.KeptBy(List(book)),
      Checking.RestsOn(Premise.BehavesAs(held), Some(NodeId("tableMatchesModel"))),
      Checking.RestsOn(Premise.OneRunAtATime(held), Some(NodeId("oneAtATime"))),
      Checking.RestsOn(Premise.Initially(held), Some(NodeId("startsEmpty"))),
      Checking.RestsOn(Premise.WrittenOnlyBy(held), Some(NodeId("onlyBookingWrites")))))
  }

  test("a booking ends after it starts: met where one is made, by book and by the table's inRoom") {
    assertEquals(checking("endsAfterStart").head, Checking.WhereMade(Ty.Data(TypeName("Booking")), List(book),
      List(held -> OpName("inRoom"))))
  }

  test("what the booking form sends is trusted: an assumption of always[Request]") {
    assertEquals(checking("requestsEndAfterStart").head, Checking.Trusted)
  }

  test("an assumption about the outside says so") {
    assertEquals(checking("oneAtATime"),
      List(Checking.Outside(frflow.core.expr.OutsideFact.OneRunAtATime(held))))
  }

  test("a claim the calendar's Scala cannot be judged by (it quantifies over moments) is proven from its parts") {
    assertEquals(checking("grantWhenFree").take(2), List(Checking.FromParts(List(NodeId("grantWhenNoOverlap"))),
      Checking.NotTested(SymbolName("granted"))))
    assert(!Checking.unchecked(t, NodeId("grantWhenFree")))
  }

  test("a claim about tested Scala reading as no call is tested whole; one with no Scala value, not checked") {
    val whole = Node.claim("A request granted is granted again with its own room's bookings only.")(
      forall((h: Term[RoomBookings], request: Term[Booking]) => granted(h, request) implies granted(
        make[RoomBookings](h.room, h.bookings.filter(b => b.room === request.room)), request)))
    val moments = Node.claim("A request granted covers no moment a booking covers.")(
      forall((h: Term[RoomBookings], request: Term[Booking]) => granted(h, request) implies free(h.bookings, request)))
    val kb = FrModel("Rooms")(whole, moments).implementTested(granted)(_ => (h, r) => Calendar(h).grants(r))
    val u = Theories.resolved(kb).theory
    assertEquals(List("whole", "moments").map(n => Checking.of(u, NodeId(n)).head), List(
      Checking.TestedAgainst(SymbolName("granted"), whole = true), Checking.NotTested(SymbolName("granted"))))
    assertEquals(List("whole", "moments").map(n => Checking.unchecked(u, NodeId(n))), List(false, true))
  }
