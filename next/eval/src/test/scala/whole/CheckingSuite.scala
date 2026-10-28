package whole

import frflow.*
import frflow.core.analysis.Premise
import frflow.core.checking.Checking
import frflow.core.code.Code
import frflow.core.consistency.Standing
import frflow.core.expr.OutsideFact
import frflow.core.name.{BoundaryName, DefName, ModelName, NodeId, OpName, SymbolName, TypeName}
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

  private val (table, booking) = (BoundaryName("bookingTable"), Ty.Data(TypeName("Booking")))
  private val fromOutside = Checking.RestsOn(Premise.FromOutside(booking), Some(NodeId("bookingsEndAfterStart")))
  private val modelled = Checking.RestsOn(Premise.BehavesAs(held), Some(NodeId("tableMatchesModel")))
  private val atomic = Checking.RestsOn(Premise.Atomic(table), Some(NodeId("oneAtATime")))
  /** The rule an assumption of `always` gives: listed, and taken, by every statement whose check rests on it. */
  private val rule = Checking.Rules(List(NodeId("bookingsEndAfterStart") -> true))

  test("a root over Declarations: proven from its parts, its rule beside them, resting on what bookings meet") {
    assertEquals(checking("bookWhenFree"), List(
      Checking.FromParts(List("bookedIsStored", "bookedAfterIsStored", "storeWhenFree").map(NodeId(_))),
      Checking.Rules(List(NodeId("neverOverlap") -> true, NodeId("bookingsEndAfterStart") -> true)),
      fromOutside))
  }

  test("what a Declaration is: book's program stands in it, nothing is proven of it, it rests on nothing") {
    assertEquals(checking("bookedAfterIsStored"), List(
      Checking.SaysWhatIs(List(SymbolName("bookedAfter")), List(book -> Code.ProvenFlow(DefName("bookIfGranted")))),
      Checking.Consistent(List("bookedAfterIsStored", "acceptedIsAnswered", "grantWhenNoOverlap").map(NodeId(_)),
        Standing.Witnessed)))
    assertEquals(checking("bookedIsStored"), List(Checking.SaysWhatIs(List(SymbolName("booked")), Nil),
      Checking.Consistent(List(NodeId("bookedIsStored")), Standing.Witnessed)))
  }

  test("what booking stores: proven of book's program, resting on the table's model, atomic runs, the form") {
    assertEquals(checking("storeWhenFree"), List(
      Checking.AgainstCode(book, Code.ProvenFlow(DefName("bookIfGranted"))),
      Checking.AssumedByCallers(List(book)), rule, modelled, atomic, fromOutside))
  }

  test("the calendar's claim: tested against granted's Scala, call by call, consistent with what reads it") {
    assertEquals(checking("grantWhenNoOverlap"), List(
      Checking.TestedAgainst(SymbolName("granted"), whole = false),
      Checking.AssumedByCallers(List(SymbolName("granted"))), rule, fromOutside,
      Checking.Consistent(List("bookedAfterIsStored", "acceptedIsAnswered", "grantWhenNoOverlap").map(NodeId(_)),
        Standing.Witnessed)))
  }

  test("what always holds: kept by every run of book, from the start, resting on the three facts about the table") {
    assertEquals(checking("neverOverlap").take(5), List(
      Checking.KeptBy(List(book)), rule, modelled, atomic,
      Checking.RestsOn(Premise.Initially(held), Some(NodeId("startsEmpty")))))
  }

  test("a room's bookings never overlap: met where a room's bookings are made, by the table's inRoom") {
    assertEquals(checking("roomBookingsApart").head, Checking.WhereMade(Ty.Data(TypeName("RoomBookings")), Nil,
      List(held -> OpName("inRoom"))))
  }

  test("what the booking form sends is trusted, and met where a booking is made: by book, by the table's inRoom") {
    assertEquals(checking("bookingsEndAfterStart").take(2), List(Checking.Trusted,
      Checking.WhereMade(booking, List(book), List(held -> OpName("inRoom")))))
  }

  test("an assumption about the outside says so; the table's model lists the programs changing it, derived") {
    assertEquals(checking("oneAtATime"), List(Checking.Outside(OutsideFact.Atomic(table))))
    assertEquals(checking("tableMatchesModel").take(2), List(Checking.Outside(OutsideFact.BehavesAs(table, held)),
      Checking.ChangedBy(List(book))))
  }

  test("a claim the calendar's Scala cannot be judged by (it quantifies over moments) is proven from its parts") {
    assertEquals(checking("grantWhenFree").take(4), List(Checking.FromParts(List(NodeId("grantWhenNoOverlap"))),
      Checking.NotTested(SymbolName("granted")), Checking.AssumedByCallers(List(SymbolName("granted"))),
      Checking.Rules(List("bookingsOfTheRoom", "roomBookingsApart", "bookingsEndAfterStart").map(NodeId(_) -> true))))
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
