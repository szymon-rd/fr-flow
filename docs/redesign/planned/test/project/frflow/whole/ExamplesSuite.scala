package whole

import frflow.*
import frflow.core.example.Example
import frflow.eval.Semantics
import frflow.eval.run.{ExampleRun, OnCode}
import frflow.proof.obligation.{Discharge, ObligationName}
import rooms.*

/** Examples as ordinary tests (owner §18): read beside the FrModel, checked against the code in Scala and
  * against the claims in Lean; nothing else depends on them.
  */
class ExamplesSuite extends munit.FunSuite:
  private val examples: List[Example] = roomsExamples.elaborated.fold(e => fail(e.toString), identity)

  private def onCode(kb: FrModel): List[OnCode] =
    val e = kb.elaborated.fold(es => fail(es.toString), identity)
    examples.map(ExampleRun(Semantics(e), e.theory).of)

  test("each example holds of the calendar's code; one a wrong calendar breaks fails") {
    assertEquals(onCode(rooms), List.fill(3)(OnCode.Holds))
    val lenient = FrModel("Rooms")(rooms.nodes*).implementProven(book)(bookIfGranted)
      .implementTested(granted)(_ => (_, _) => true)
    assertEquals(onCode(lenient), List(OnCode.Holds, OnCode.Fails, OnCode.Holds))
  }

  test("against the claims, in Lean: for every meaning of granted the claims about it allow, the example holds") {
    val w = Whole(rooms, examples)
    val asked = w.obligations.filter(_.name == ObligationName.Example(0))
    assertEquals(asked.map(_.discharge), List(Discharge.Attempt(20000)))
    assert(w.lean.exists(_.contains("def example_0 : Prop :=\n  ∀ (granted : RoomBookings → Booking → Prop), " +
      "(Rooms.grantWhenFree.claim granted) → (Rooms.grantWhenNoOverlap.claim granted) → " +
      "(granted (RoomBookings.mk [(Booking.mk \"Oak\" 9 10)]) (Booking.mk \"Oak\" 10 11))")), w.lean)
  }

  test("nothing in the FrModel depends on an example: its theory and obligations are the same without them") {
    val aboutExamples: ObligationName => Boolean = { case ObligationName.Example(_) => true; case _ => false }
    val (withThem, without) = (Whole(rooms, examples), Whole(rooms, Nil))
    assertEquals(withThem.obligations.filterNot(o => aboutExamples(o.name)).map(o => (o.name, o.doc)),
      without.obligations.map(o => (o.name, o.doc)))
    assertEquals(withThem.lean.filterNot(_.contains("example_")), without.lean)
  }

  test("an example giving a provided Definition a value is checked in Scala only, and shown so") {
    val setting = auth.authExamples.elaborated.fold(e => fail(e.toString), identity)
    val e = auth.knowledge.elaborated.fold(es => fail(es.toString), identity)
    assertEquals(setting.map(ExampleRun(Semantics(e), e.theory).of), List(OnCode.Holds))
    assertEquals(Whole(auth.knowledge, setting).obligations.filter(_.name == ObligationName.Example(0)), Nil)
    assertEquals(frflow.wire.snapshot.Rows.example(setting.head, None, OnCode.Holds).onClaims, "checked in Scala only")
  }
