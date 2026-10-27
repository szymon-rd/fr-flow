package rooms

import cats.syntax.all.*
import frflow.*
import frflow.core.analysis.{Problem, Resolve, Validate}
import frflow.core.analysis.{Premise, Premises}
import frflow.core.name.{DefName, KbName, ModelName, NodeId, SymbolName}
import frflow.proof.lean.ast.{LeanName, Names}
import frflow.proof.lean.lower.{LowerEnv, LowerModels, LowerObligation, LowerProp, Naming}
import frflow.proof.lean.print.PrintDecl
import frflow.proof.obligation.{Idle, Required}
import frflow.proof.terms.TermTable

/** The owner's root for rooms (§9), one idea per statement (§10): booking in two claims about the `book` program,
  * proven from its parts (the calendar's claims) by its code's `impl`, on the store's model; every check resting on
  * the world outside lists the assumptions saying it with `.assuming`, the one mechanism for a premise (§15, §16,
  * §17), and the list is checked against what the check rests on.
  */
class BookSuite extends munit.FunSuite:
  private def valid(kb: FrModel) = kb.elaborated.fold(e => fail(e.toString), Validate(_))
  private val all = List(bookWhenFree, answersWhetherBooked, grantWhenFree, grantWhenNoOverlap, neverOverlap,
    endsAfterStart, roomBookingsApart, storeModel, startsEmpty, onlyBookingWrites, oneAtATime, fromTheForm)
  private def problems(nodes: List[Node]) = valid(FrModel("Rooms")(nodes*).implementProven(book)(bookIfGranted)
    .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))).fold(_.toList, _ => Nil)

  private val strayPart = Node.claim("Every booking ends after it starts.")(
    forall((b: Term[Booking]) => b.start < b.end))
    .refines(bookWhenFree)
  private val outsideAsPart = Node.assumption("The store keeps what it is given.")(store.behavesAs(stored))
    .refines(bookWhenFree)
  private val assumingAClaim = Node.claim("Granted for a room with no bookings.")(
    forall((held: Term[RoomBookings], request: Term[Booking]) =>
      granted(held, request) === isFree(held.bookings, request)))
    .refines(grantWhenFree).assuming(grantWhenFree)
  private val grantedRoot = Node.claim("A request is granted exactly when its room is free.")(
    forall((held: Term[RoomBookings], request: Term[Booking]) =>
      granted(held, request) === isFree(held.bookings, request)))
  private val bookingAgrees = Node.claim("Booking answers as the calendar grants, on the room's bookings held.")(
    forall((request: Term[Request], before: Term[World]) => book(request).from(before) { (booked, _) =>
      booked === granted(make[RoomBookings](stored.in(before).filter(b => b.room === request.room)),
        asBooking(request)) }))
    .assuming(storeModel, oneAtATime, fromTheForm)
  private val unassumed = Node.claim("Booking answers whether the request was booked, said again.")(
    forall((request: Term[Request], before: Term[World]) =>
      book(request).from(before) { (booked, after) => booked === (stored.in(after) =!= stored.in(before)) }))
  private val overAssumed = Node.claim("A request is granted exactly when its room is free, said again.")(
    forall((held: Term[RoomBookings], request: Term[Booking]) =>
      granted(held, request) === isFree(held.bookings, request)))
    .assuming(oneAtATime)
  private val nobodyWrites = Node.assumption("Nothing writes the store.")(stored.writtenOnlyBy())
  private val formAssumed = Node.claim("A request is granted exactly when its room is free, said a third time.")(
    forall((held: Term[RoomBookings], request: Term[Booking]) =>
      granted(held, request) === isFree(held.bookings, request)))
    .assuming(fromTheForm)
  // A Definition taking a Booking from outside: its Bookings are made by no covered code (owner §21).
  private val cancels = Definition[Booking => Boolean]("whether a booking may be cancelled")
  private val cancelsWhenFuture = Node.claim("A booking may be cancelled exactly when it ends after it starts.")(
    forall((b: Term[Booking]) => cancels(b) === (b.start < b.end)))
  private val fromTheDesk = Node.assumption("The front desk passes only bookings that end after they start.")(
    always[Booking](b => b.start < b.end))

  test("the root statements: booking's two (one idea each) and what always holds, none with a parent") {
    val v = valid(rooms).fold(ps => fail(ps.toString), identity)
    assertEquals(v.theory.refinement.roots.map(_.id.value),
      List("bookWhenFree", "answersWhetherBooked", "neverOverlap", "endsAfterStart", "roomBookingsApart"))
  }

  test("several roots are allowed (owner §11): one on another Definition, and one relating two") {
    assertEquals(problems(all ++ List(grantedRoot, bookingAgrees)), Nil)
  }

  test("each claim of booking is one equation: the store after, by a conditional; the answer, by the store") {
    val posts = List(bookWhenFree, answersWhetherBooked).map(n => RoomsLean.define(RoomsLean.post(n.statement)))
    assertEquals(posts, List(
      "(request : Request) (result : Prop) (before : World) (after : World) := (after.database = " +
        "(if (Rooms.isFree before.database (Rooms.asBooking request)) then " +
        "(before.database ++ [(Rooms.asBooking request)]) else before.database))",
      "(request : Request) (booked : Prop) (before : World) (after : World) := " +
        "(booked = (¬(after.database = before.database)))"))
  }

  test("each check rests on the outside facts its .assuming lists; derived, the list is checked, never filled in") {
    val premises = Validate(rooms.elaborated.fold(e => fail(e.toString), identity)).fold(ps => fail(ps.toString),
      v => List("bookWhenFree", "neverOverlap", "endsAfterStart", "roomBookingsApart").map(n =>
        Premises.of(v.theory, NodeId(n))))
    val (m, form) = (ModelName("stored"), Premise.FromOutside(LeanType[Request].ty))
    val kept = List(Premise.BehavesAs(m), Premise.OneRunAtATime(m), Premise.Initially(m), Premise.WrittenOnlyBy(m))
    assertEquals(premises, List(List(Premise.BehavesAs(m), Premise.OneRunAtATime(m), form), kept :+ form,
      kept :+ form, List(Premise.BehavesAs(m))))
    assertEquals(problems(all :+ unassumed), List(
      Problem.PremiseMissing(NodeId("unassumed"), Premise.BehavesAs(m), Some(NodeId("storeModel"))),
      Problem.PremiseMissing(NodeId("unassumed"), Premise.OneRunAtATime(m), Some(NodeId("oneAtATime"))),
      Problem.PremiseMissing(NodeId("unassumed"), form, Some(NodeId("fromTheForm")))))
    assertEquals(problems(all :+ overAssumed),
      List(Problem.PremiseNotNeeded(NodeId("overAssumed"), NodeId("oneAtATime"))))
    assertEquals(problems(all.filterNot(_ == onlyBookingWrites) :+ nobodyWrites).collect {
      case p: Problem.WriterNotListed => p }, List(Problem.WriterNotListed(m, SymbolName("book"))))
  }

  test("values from outside (owner §21): an assumption of `always` on their type, listed where a check rests on it") {
    val (booking, deskId) = (LeanType[Booking].ty, NodeId("fromTheDesk"))
    val desk = FrModel("Rooms")((all :+ cancelsWhenFuture)*).implementProven(book)(bookIfGranted)
      .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))
      .implementTested(cancels)(_ => b => b.start < b.end)
    def problemsOf(kb: FrModel) = valid(kb).fold(_.toList, _ => Nil)
    assertEquals(problemsOf(desk),
      List(Problem.PremiseMissing(NodeId("endsAfterStart"), Premise.FromOutside(booking), None)))
    // Every check whose Lean form carries a Booking's guard (a Booking bound, or the store) now rests on the desk.
    assertEquals(problemsOf(desk.copy(nodes = desk.nodes :+ fromTheDesk)).collect {
      case Problem.PremiseMissing(id, Premise.FromOutside(`booking`), Some(`deskId`)) => id.value },
      List("bookWhenFree", "answersWhetherBooked", "grantWhenFree", "grantWhenNoOverlap", "neverOverlap",
        "endsAfterStart", "roomBookingsApart", "cancelsWhenFuture"))
    assertEquals(problems(all :+ formAssumed),
      List(Problem.PremiseNotNeeded(NodeId("formAssumed"), NodeId("fromTheForm"))))
    val r = Resolve(valid(rooms).fold(ps => fail(ps.toString), identity))
    assertEquals((Required.keeps(r, NodeId("endsAfterStart")).nonEmpty,
      Required.made(r, NodeId("endsAfterStart")).map(_.name.toString)), (true, List("Made(inRoom)")))
    assertEquals(Premises.of(r.theory, NodeId("grantWhenFree")), Nil)
  }

  test("a fact about the outside is a premise, never a part; a premise is an assumption or an `always`") {
    assertEquals(problems(all :+ outsideAsPart),
      List(Problem.OutsideAsPart(NodeId("outsideAsPart"), NodeId("bookWhenFree"))))
    assertEquals(problems(all :+ assumingAClaim),
      List(Problem.PremiseNotAssumed(NodeId("assumingAClaim"), NodeId("grantWhenFree"))))
  }

  test("a part of proven code that is not a statement about what the code calls is refused") {
    assertEquals(problems(all :+ strayPart), List(Problem.PartNotCalled(NodeId("bookWhenFree"), NodeId("strayPart"))))
  }

  test("impl is the root's step from its parts: complete is asked of the calendar's claim, not of the root; no idle") {
    val r = Resolve(valid(rooms).fold(ps => fail(ps.toString), identity))
    val (root, calendar) = (NodeId("bookWhenFree"), NodeId("grantWhenFree"))
    assertEquals((Required.complete(r, root).isDefined, Required.complete(r, calendar).isDefined), (false, true))
    val table = TermTable.of(r)
    val impl = Required.impl(r, root).map(o => PrintDecl(LowerObligation(LowerProp(table, env(table)))(o)))
    assertEquals(Idle.of(r, table, root), None)
    assertEquals(impl, List("namespace Obl\n\n" +
      "/-- Every result of bookIfGranted_run meets bookWhenFree, given what grantWhenFree promise. -/\n" +
      "@[frflow_defs] def impl : Prop :=\n" +
      "  ∀ (granted : RoomBookings → Booking → Prop), " +
      "∀ (h_grantWhenFree : (Rooms.grantWhenFree.claim granted)), " +
      "(Rooms.bookWhenFree.claim (Rooms.bookIfGranted_run granted))\n\nend Obl"))
  }

  test("the store's model and the program's run on it, as Lean: the run is defined over the model's operations") {
    val e = rooms.elaborated.fold(es => fail(es.toString), identity)
    val r = Resolve(valid(rooms).fold(ps => fail(ps.toString), identity))
    val (v, table) = (e.theory.vocabulary, TermTable.of(r))
    val lean = LowerModels(env(table), Naming.over(Set("granted"), Set("Booking", "World")))
    val worlds = v.models.flatMap(m => v.boundary(m.boundary).map(_ -> m))
    val run = v.define(DefName("bookIfGranted_run")).map(d => lean.run(d, DefName("bookIfGranted"),
      table.defines(d.name).symbols.map(s => s -> table.typeOf(s))))
    assertEquals(lean.decls(worlds).map(PrintDecl(_)).mkString("", "\n\n", "\n"),
      RoomsLean.golden("Boundaries.decls.lean"))
    assertEquals(run.map(PrintDecl(_) + "\n"), Some(RoomsLean.golden("Def_bookIfGranted_run.decl.lean")))
  }

  private def env(table: TermTable) = LowerEnv(KbName("Rooms"), opens(table), _ => Names.builtin("store"),
    _ => Names.builtin("Bookings"), _ => None)

  private def opens(table: TermTable)(d: DefName): List[LeanName] =
    table.defines.get(d).toList.flatMap(_.symbols.map(s => Names.ident(s.value)))
