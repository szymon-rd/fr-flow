package frflow.project.assumed

import frflow.core.analysis.Problem
import frflow.core.analysis.outside.Guards
import frflow.core.expr.{Expr, Exprs}
import frflow.core.name.{ModelName, NodeId, SymbolName}
import frflow.eval.assumed.{Beside, Picking}
import frflow.proof.obligation.{ObligationName, Required}
import frflow.proof.terms.CallingCode
import whole.Theories

/** What an operation known only by assumptions may not be made to say (G2, the step 13c review): what is assumed of
  * it reads its own model only (`ReadsBeside`, B1); a claim of always does not cover what it gives, values from
  * outside (`AssumedMakes`, B2, owner §37); a claim about it is proven from what is assumed of it, never taken in its
  * place by code calling it (B3), and is asked of the models' meanings (`impl`) where nothing else checks it. What
  * such an operation gives, handed on, carries the guards of what values from outside meet, not a claim's (B2's R5).
  */
class RefusedSuite extends munit.FunSuite:
  private def id(n: String) = NodeId(n)

  test("an assumption about a draw reading another model is refused; one about what the draw is handed is not") {
    assertEquals(Theories.problems(Beside.reading),
      List(Problem.ReadsBeside(id("drawnFresh"), SymbolName("draw"), ModelName("register"))))
    assertEquals(Theories.problems(Beside.handed), Nil)
  }

  test("a claim of always on what an operation known only by assumptions gives is refused (Picked2, Picked)") {
    val refused = List(Problem.AssumedMakes(id("posRule"), SymbolName("pick")))
    assertEquals(Theories.problems(Picking.Ruled.knowledge), refused)
    assertEquals(Theories.problems(Picking.Circle.knowledge), refused)
  }

  test("code calling an operation known only by assumptions relies on what is assumed of it, not on a claim about it") {
    val r = Theories.resolved(Picking.apart)
    assertEquals(r.reliesOn(id("takenPositive")), List(id("pickKeeps")))
    assertEquals(Required.hypotheses(r, id("takenPositive")), List(id("pickKeeps")))
    assertEquals(r.reliedOnBy(SymbolName("take")), List(id("pickKeeps")))
  }

  test("a claim about operations on a state alone is asked impl, given what is assumed of the one it reads") {
    val r = Theories.resolved(Picking.lone)
    assertEquals(Required.of(r, Set.empty, id("pickedPositive")).map(_.name), List(ObligationName.Impl))
    assertEquals(Required.hypotheses(r, id("pickedPositive")), List(id("pickKeeps")))
    assertEquals(Required.of(Theories.resolved(Picking.AsPart.knowledge), Set.empty, id("pickedPositive")).map(_.name),
      List(ObligationName.Impl))
  }

  test("a result from outside handed on carries what values from outside meet, never a claim's rule (owner §37)") {
    val t = Theories.theory(Picking.Handed.knowledge)
    val guards = Guards.byAlways(t).toMap
    val call = CallingCode.of(t).find(_.definition == SymbolName("pass")).getOrElse(fail("no call of plain Scala"))
    def named(rule: String) = Exprs.all(call.formula(1, guards(id("posRule"))).value).count {
      case Expr.Call(d, _, _) => d.value == rule
      case _                  => false
    }
    assertEquals((named("posFromOutside"), named("posRule")), (1, 1))
  }
