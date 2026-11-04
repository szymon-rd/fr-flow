package frflow.vocab

import frflow.*
import frflow.core.code.Values
import frflow.core.expr.{Expr, Iteration, PrimOp}
import frflow.core.name.SymbolName
import frflow.core.expr.Renamed
import frflow.dsl.term.Lift
import frflow.eval.Env
import frflow.eval.term.Evaluate
import frflow.vocab.CountSyntax.*

/** A vocabulary added outside the core module: `count`, used in a term as the core's operations are. */
class CountSuite extends munit.FunSuite:
  private val xs = Lift.constant(List(BigInt(1), BigInt(5), BigInt(7)))
  private val big = xs.count(x => (4: Term[BigInt]) < x)
  private val env = Env.of(Values.none)

  test("an interpreter that knows `count` runs its own; one that does not runs its semantics; both give 2") {
    val counting = Counting()
    assertEquals((counting.of(big.run)(env), Evaluate.of(big.run)(env)), (Right(BigInt(2)), Right(BigInt(2))))
    assertEquals(counting.calls.get, 1)
  }

  test("a transformer over an interpreter that knows `count` runs its meaning: the same value, not its own") {
    val counting = Counting()
    assertEquals(big.run(Renamed(counting, identity, (s: SymbolName) => s))(env), Right(BigInt(2)))
    assertEquals(counting.calls.get, 0)
  }

  test("the IR of a term using `count` is its semantics in the core language: the length of a filter") {
    big.expr match
      case Expr.Prim(PrimOp.Length, List(Expr.Iterate(Iteration.Filter, _, x, _, _)), _) => assertEquals(x.hint, "x")
      case other => fail(s"not a filter's length: $other")
  }
