package rooms

import frflow.*
import frflow.core.code.Values
import frflow.core.expr.{Expr, Exprs, Lambda}
import frflow.core.name.{SymbolName, VarId}
import frflow.core.spec.Form
import frflow.core.term.interpret.Hypotheses
import frflow.eval.NotEvaluated
import frflow.proof.lean.print.Print
import frflow.proof.lean.term.{LeanTerm, Scope}
import scala.util.Try

/** The README's rooms model as a user writes it (`Rooms.scala`): elaborated, printed as Lean from its terms, run as
  * Scala by the evaluator; names from the vals as written, a claim on a Definition read as its call.
  */
class RoomsSuite extends munit.FunSuite:
  import RoomsLean.{define, elaborated}

  private val noOverlaps = frflow.define { (held: Term[List[Booking]]) => held.pairwise(noOverlap) }
  private val unrepeated = frflow.define { (held: Term[List[Booking]]) => held.allDistinct }

  test("names come from the vals as written: the node `grantWhenFree`, the Definition `granted`") {
    assertEquals((grantWhenFree.head.id.value, granted.name.value), ("grantWhenFree", "granted"))
  }

  test("the claim is one equation, and prints as Lean with each define called by name") {
    val claim = elaborated(grantWhenFree.statement).said.map(RoomsLean.formula)
    assertEquals(claim, Some("(∀ (held : RoomBookings), (∀ (request : Booking), " +
      "((granted held request) = (Rooms.isFree held.bookings request))))"))
  }

  test("a define prints once as its own def, over its inputs; a define passed as a function is applied to each") {
    assertEquals(define(elaborated(RoomsLean.lambda(isFree))), "(held : (List Booking)) (request : Booking) := " +
      "(∀ b ∈ held, (Rooms.apart b request))")
  }

  test("a define's IR binds its inputs at levels 0 and 1 and its own binders past them") {
    val l: Lambda = elaborated(RoomsLean.lambda(apart)).value
    assertEquals(l.params.map(_.id), List(VarId.level(0), VarId.level(1)))
    assert(Exprs.all(l.body).exists { case Expr.Quant(_, List(x), _) => x.id.value == 2; case _ => false })
  }

  test("the calendar's words run as Scala on calendars, by the evaluator; the root's, over every moment, do not") {
    val ok = frflow.define { (held: Term[List[Booking]], r: Term[Booking]) => held.forall(b => noOverlap(b, r)) }
    assert(ok.fn(Values.none)(List(Booking("Oak", 9, 10)), Booking("Oak", 10, 11)))
    assert(!ok.fn(Values.none)(List(Booking("Oak", 9, 11)), Booking("Oak", 10, 12)))
    val overMoments = Try(isFree.fn(Values.none)(List(Booking("Oak", 1, 2)), Booking("Oak", 9, 10)))
    assert(overMoments.failed.toOption.exists(_.isInstanceOf[NotEvaluated]), overMoments)
    val (calendar, distinct) = (noOverlaps.fn(Values.none), unrepeated.fn(Values.none))
    val (oak, elm) = (Booking("Oak", 9, 11), Booking("Elm", 9, 11))
    assertEquals(List(List(oak, elm), List(oak, oak.copy(start = 10))).map(calendar), List(true, false))
    assertEquals(List(List(oak, elm), List(oak, oak)).map(distinct), List(true, false))
  }

  test("pairwise and allDistinct print as Lean's List.Pairwise and List.Nodup") {
    assertEquals((define(elaborated(RoomsLean.lambda(noOverlaps))), define(elaborated(RoomsLean.lambda(unrepeated)))),
      ("(held : (List Booking)) := (List.Pairwise (fun (a : Booking) (b : Booking) => (Rooms.noOverlap a b)) held)",
        "(held : (List Booking)) := (List.Nodup held)"))
  }

  test("a claim on a Definition reads as its call: the Definition found, the post over the call's inputs") {
    val call = RoomsLean.call(grantWhenNoOverlap.statement)
    assertEquals(call.definition, SymbolName("granted"))
    assertEquals(call.posted.value.params.map(_.hint), List("held", "request"))
  }

  test("the answer the claim fixes, for the step refutation: the right side of `granted(held, request) === …`") {
    val post = RoomsLean.post(grantWhenNoOverlap.statement)
    val e = frflow.testing.search.StepRefutation.answerOf(post.value, granted.name)
    assertEquals(e.map(_.toString.contains("granted")), Some(false))
    assert(e.exists(_.toString.contains("Iterate(Forall")), e)
  }

  test("the claim's post is one equation, no hypothesis: what always holds of a booking is its `always`'s") {
    val post = RoomsLean.post(grantWhenNoOverlap.statement)
    val (names, scope) = Scope.over(post.value.params, RoomsLean.naming)
    val printed = post.form match
      case Form.Term(t) =>
        val (hs, c) = Hypotheses.of(t.run, LeanTerm(RoomsLean.env))
        (hs.map(h => Print.expr(h(scope))), Print.expr(c(scope)))
      case Form.Steps(_) => fail("not a term")
    assertEquals(names.map(_.text), List("held", "request"))
    assertEquals(printed, (Nil, "((granted held request) = (∀ b ∈ held.bookings, (Rooms.noOverlap b request)))"))
  }
