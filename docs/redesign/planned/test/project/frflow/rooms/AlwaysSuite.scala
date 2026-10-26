package rooms

import frflow.core.analysis.{Guards, Resolve, Validate}
import frflow.core.name.{DefName, KbName, ModelName, NodeId, TypeName}
import frflow.core.spec.Range
import frflow.core.ty.Ty
import frflow.eval.run.{Broken, CallCheck, Made}
import frflow.eval.{Env, ScalaValue, Semantics}
import frflow.core.code.Values
import frflow.proof.lean.ast.Names
import frflow.proof.lean.lower.{LowerEnv, LowerKeeps, LowerObligation, LowerProp, Naming}
import frflow.proof.lean.print.{Print, PrintDecl}
import frflow.proof.lean.term.Printed
import frflow.proof.obligation.{Prop, Required}
import frflow.proof.terms.TermTable

/** The second quantifier (owner §15, §16): `always[T]`, every value of `T` that can be made, and `always(stored)`,
  * every state the store reaches. Each is its own claim and a hypothesis of every statement in Lean; one is met where a
  * value is made (at a tested Definition's boundary in Scala), the other kept by every program writing the store.
  */
class AlwaysSuite extends munit.FunSuite:
  private val e = rooms.elaborated.fold(es => fail(es.toString), identity)
  private val r = Resolve(Validate(e).fold(ps => fail(ps.toString), identity))
  private val table = TermTable.of(r)
  private val env = LowerEnv(KbName("Rooms"), _ => Nil, _ => Names.builtin("store"), _ => Names.builtin("Bookings"),
    _ => None)
  private val naming = Naming.over(Set("granted", "book"), Set("Booking", "World"))

  test("each `always` is its own claim: over what can be made, or what the store reaches; each a root statement") {
    val ranges = List(endsAfterStart, neverOverlap).map(n => RoomsLean.elaborated(n.statement).range)
    assertEquals(ranges, List(Some(Range.Made(Ty.Data(TypeName("Booking")))),
      Some(Range.Reached(List(ModelName("stored"))))))
    assert(e.theory.vocabulary.define(DefName("endsAfterStart")).isDefined)
    assertEquals(r.theory.refinement.roots.filter(_.statement.range.exists(_ != Range.Possible)).map(_.id.value),
      List("neverOverlap", "endsAfterStart", "roomBookingsApart"))
  }

  test("in Lean, every booking a statement is about comes with what always holds of bookings as a hypothesis") {
    val claim = RoomsLean.elaborated(grantWhenFree.statement).said.map(f =>
      Print.expr(Printed.claim(env, naming, Guards.of(r.theory))(f.term)))
    assertEquals(claim, Some("(∀ (held : RoomBookings), ((∀ b ∈ held.bookings, (Rooms.endsAfterStart b)) → " +
      "((Rooms.roomBookingsApart held) → (∀ (request : Booking), ((Rooms.endsAfterStart request) → " +
      "((granted held request) = (Rooms.isFree held.bookings request)))))))"))
  }

  test("every run of booking's code keeps each `always` about the store, from a world meeting them all") {
    val keeps = List("neverOverlap", "endsAfterStart").flatMap(n => Required.keeps(r, NodeId(n)))
    val printed = keeps.map(o => PrintDecl(LowerObligation(LowerProp(table, env))(o)))
    val decls = keeps.map(_.goal).collect { case Prop.Forall(_, Prop.Implies(_, k: Prop.Keeps)) =>
      PrintDecl(LowerKeeps(env, table, naming)(k)) }
    assertEquals(printed, List("neverOverlap", "endsAfterStart").map(i => "namespace Obl\n\n" +
      s"/-- Every run of bookIfGranted_run keeps $i, given what grantWhenFree, grantWhenNoOverlap promise. -/\n" +
      "@[frflow_defs] def cover_book : Prop :=\n  ∀ (granted : RoomBookings → Booking → Prop), " +
      "∀ (h_grantWhenFree : (Rooms.grantWhenFree.claim granted)) " +
      "(h_grantWhenNoOverlap : (Rooms.grantWhenNoOverlap.claim granted)), " +
      s"(Rooms.$i.keeps_book (Rooms.bookIfGranted_run granted))\n\nend Obl"))
    assertEquals(decls.map(_ + "\n"), List("neverOverlap", "endsAfterStart").map(i =>
      RoomsLean.golden(s"Keeps_$i.decl.lean")))
    assertEquals(Required.keeps(r, NodeId("answersWhetherBooked")), Nil)
  }

  test("at a tested Definition's boundary, a booking that ends before it starts breaks `endsAfterStart`") {
    val semantics = Semantics(e)
    val made = Made.of(semantics, e.theory)
    val (bad, good) = (Booking("Oak", 11, 9), Booking("Oak", 9, 11))
    val ends = made.find(_.always.value == "endsAfterStart").getOrElse(fail("endsAfterStart"))
    assertEquals((ends.holds(ScalaValue(bad), Env.of(Values.none)), ends.holds(ScalaValue(good), Env.of(Values.none))),
      (false, true))
    val check = CallCheck.of(semantics, e.theory, NodeId("grantWhenNoOverlap")).getOrElse(fail("a call"))
    def broken(held: RoomBookings, request: Booking) =
      check.always(List(held, request, true).map(ScalaValue(_)), Env.of(Values.none))
    assertEquals(broken(RoomBookings(Nil), bad), Some(Broken.Always(NodeId("endsAfterStart"))))
    assertEquals(broken(RoomBookings(List(bad)), good), Some(Broken.Always(NodeId("endsAfterStart"))))
  }

  test("what the store can give always holds: two overlapping bookings of a room are no RoomBookings it gives") {
    val made = Made.of(Semantics(e), e.theory).find(_.always.value == "roomBookingsApart").getOrElse(fail("made"))
    val (a, b) = (Booking("Oak", 9, 11), Booking("Oak", 10, 12))
    assertEquals(List(RoomBookings(List(a)), RoomBookings(List(a, b)), RoomBookings(List(a, b.copy(room = "Elm"))))
      .map(r => made.holds(ScalaValue(r), Env.of(Values.none))), List(true, false, true))
  }

  test("made_inRoom: every RoomBookings the store's model gives meets roomBookingsApart, on a world meeting all") {
    val made = Required.made(r, NodeId("roomBookingsApart"))
    assertEquals(made.map(o => PrintDecl(LowerObligation(LowerProp(table, env))(o))), List("namespace Obl\n\n" +
      "/-- Every result of stored's inRoom meets roomBookingsApart, on a world meeting what always holds. -/\n" +
      "@[frflow_defs] def made_inRoom : Prop :=\n  (Rooms.roomBookingsApart.makes_inRoom Rooms.Stored.inRoom_of)\n\n" +
      "end Obl"))
    val decls = made.map(_.goal).collect { case Prop.Forall(_, k: Prop.Makes) =>
      PrintDecl(LowerKeeps(env, table, naming).makes(k)) }
    assertEquals(decls, List("namespace Rooms.roomBookingsApart\n\n@[frflow_defs] def makes_inRoom (inRoom : " +
      "String → (List Booking) → RoomBookings) : Prop :=\n  (∀ (room : String), (∀ (w : World), " +
      "((Rooms.neverOverlap w.store) → ((∀ b ∈ w.store, (Rooms.endsAfterStart b)) → " +
      "(Rooms.roomBookingsApart (inRoom room w.store))))))\n\nend Rooms.roomBookingsApart"))
    assertEquals(Required.made(r, NodeId("endsAfterStart")).map(_.name.toString), List("Made(inRoom)"))
  }
