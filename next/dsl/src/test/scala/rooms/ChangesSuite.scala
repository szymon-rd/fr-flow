package rooms

import frflow.*
import frflow.core.expr.{Expr, Exprs, Pattern}

/** Matching an enum, a record made and updated, the folds and `let` (`Changes.scala`), each read by the analyses as
  * IR, with no cast anywhere. (Their Lean is `next-proof`'s; their values, `next-eval`'s.)
  */
class ChangesSuite extends munit.FunSuite:
  private def body(d: Definition[?]): Expr = RoomsIr.lambda(d).value.body
  private def patterns(d: Definition[?]): List[(String, List[String])] =
    Exprs.all(body(d)).collect { case Expr.Match(_, arms, _) => arms.map(_.pattern) }.flatten.map {
      case Pattern.Ctor(_, c, xs) => c.value -> xs.map(_.hint)
      case p                      => p.toString -> Nil
    }

  test("in the IR, a match binds each case's fields as its pattern's variables, named by the developer's names") {
    assertEquals(patterns(afterChange), List("Book" -> List("b"), "Cancel" -> List("room", "start"), "Clear" -> Nil))
  }

  test("a match whose first arm is a case without fields, named by its type, has the same arms") {
    assertEquals(patterns(clearedFirst).toSet, patterns(afterChange).toSet)
  }

  test("a record updated is a copy of it, one field at a time") {
    assertEquals(Exprs.all(body(moved)).collect { case Expr.Copy(_, d, us) => (d.value, us.map(_._1)) },
      List(("Booking", List(2)), ("Booking", List(1))))
  }

  test("a fold, a record made and shared by `let`, an option's and an either's fold, as IR") {
    assert(Exprs.all(body(booked)).exists { case Expr.Fold(_, _, acc, x, _) => (acc.hint, x.hint) == ("n", "b")
      case _ => false })
    assert(Exprs.all(body(hourLong)).exists {
      case Expr.Let(x, Expr.Make(_, c, _), _) => x.hint == "b" && c.value == "mk"
      case _ => false })
    assertEquals(List(startOr, outcome).map(d => Exprs.all(body(d)).count { case Expr.Match(_, _, _) => true
      case _ => false }), List(1, 1))
  }

  test("each define's IR is typed as its body") {
    assertEquals(List(afterChange, moved, booked, hourLong, startOr, outcome).map(d => Exprs.typeOf(body(d))),
      List(afterChange, moved, booked, hourLong, startOr, outcome).map(d => RoomsIr.lambda(d).value.result))
  }
