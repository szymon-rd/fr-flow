package rooms

import frflow.*
import frflow.core.name.NodeId
import frflow.eval.Semantics
import frflow.eval.run.Broken
import frflow.testing.{Plan, PropertyTests, Seed, Settings}
import frflow.testing.derive.Derive
import frflow.testing.report.Failure

/** A claim about a program's runs evaluated in Scala: the proven program's value is its run on the models
  * (`ProgramRun`), from each generated world, each model's state meeting what always holds of the store.
  */
class RunsSuite extends munit.FunSuite:
  /** A booking program that adds every request, granted or not, and says it booked it. */
  private final class AddsAll[F[_]](table: BookingTable[F, Term])(using f: Flow[F]):
    def run(request: Term[Request]): F[Term[Boolean]] = f.as(table.add(asBooking(request)), True)

  private val addsAll = program { (request: Term[Request]) => AddsAll(bookingTable.recording).run(request) }

  /** What booking answers and stores, in start and end times (rooms' own say "free", over every moment, which has no
    * Scala value).
    */
  private val answerWhenApart = Node.claim("A request is answered booked exactly when it overlaps no booking stored.")(
    forall((request: Term[Request], before: Term[World]) => book(request).from(before) { (booked, _) =>
      booked === storedBookings.in(before).forall(b => noOverlap(b, asBooking(request))) }))
  private val storeWhenApart = Node.claim("A request is stored exactly when it overlaps no booking stored.")(
    forall((request: Term[Request], before: Term[World]) =>
      val stored = storedBookings.in(before)
      book(request).from(before) { (_, after) => storedBookings.in(after) ===
        when(stored.forall(b => noOverlap(b, asBooking(request))))(stored :+ asBooking(request)).otherwise(stored) }))

  private def booking(meaning: Definition[Request => Program[Boolean]]) =
    KnowledgeBase("Rooms")((rooms.nodes :+ answerWhenApart :+ storeWhenApart)*).copy(generators = rooms.generators)
      .implementProven(book)(meaning)
      .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))

  private def tested(kb: KnowledgeBase, claim: String) =
    val e = kb.elaborated.fold(es => fail(es.toString), identity)
    PropertyTests(Semantics(e), e.theory).of(NodeId(claim), Plan(Settings(300, Seed(1)), Nil), Derive.of(e, Nil))
      .getOrElse(fail(s"$claim is not tested"))

  test("booking's program meets what booking stores and answers, run from 300 generated worlds") {
    List("answerWhenApart", "storeWhenApart").foreach(c => assertEquals(tested(booking(bookIfGranted), c).failure,
      None, c))
  }

  test("a claim over every moment has no Scala value: rooms' own is not evaluated") {
    assertEquals(tested(rooms, "bookWhenFree").failure.collect { case Failure.Call(_, _, b, _) => b },
      Some(Broken.NotEvaluated(frflow.eval.EvalError.Quantified)))
  }

  test("a program that books every request breaks what booking stores, on a generated world it clashes in") {
    assertEquals(tested(booking(addsAll), "storeWhenApart").failure.collect { case Failure.Call(_, _, b, _) => b },
      Some(Broken.Post))
  }
