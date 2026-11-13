package frflow.eval.term

import frflow.core.Lang
import frflow.core.code.Values
import frflow.core.expr.{LawSeeds, Terms, Tm, Value}
import frflow.core.term.{Bound, Selector}
import frflow.core.term.interpret.{Simplified, ToExpr}
import frflow.core.term.language.{Final, Sym}
import frflow.eval.Env
import frflow.proof.prover.laws.MoreTerms

/** `Simplified`, the optimization by `fwd` and `bwd`: a term has the value it had, on the terms the laws generate;
  * and what it takes out is gone: a part of a pair just made, an `if` on a truth value written out, a `let` of a
  * variable, a list joined with none.
  */
class SimplifiedSuite extends munit.FunSuite:
  private val big = Lang.big
  private def num[T[_]](s: Sym[T], n: Int): T[BigInt] = s.lit(BigInt(n), Value.Num(n), big)
  private def same[A](simplified: Final[A], expected: Final[A]): Unit =
    assertEquals(ToExpr.of(Simplified.of(simplified)), ToExpr.of(expected))

  test("a term simplified has the value it had, on the terms the laws generate") {
    val generated = LawSeeds(600).flatMap(seed => List(Tm.closed(Terms(seed).bool(3, 0)), MoreTerms(seed).formula))
      .map(Closed.of)
    val env = Env.of(Values.none)
    val valued = generated.filter(t => Evaluate.of(t)(env).isRight)
    assert(valued.size >= 700, valued.size)
    assertEquals(valued.count(t => Evaluate.of(Simplified.of(t))(env) != Evaluate.of(t)(env)), 0)
  }

  test("a part of a pair just made is that part, and an if on a truth value written out its branch") {
    same([T[_]] => (s: Sym[T]) => s.field(s.pair(num(s, 1), num(s, 2)), Selector.second[BigInt, BigInt](big)),
      [T[_]] => (s: Sym[T]) => num(s, 2))
    same([T[_]] => (s: Sym[T]) => s.cond(s.not(s.bool(false)), num(s, 1), num(s, 2)),
      [T[_]] => (s: Sym[T]) => num(s, 1))
    same([T[_]] => (s: Sym[T]) => s.and(s.bool(true), s.lt(num(s, 1), num(s, 2))),
      [T[_]] => (s: Sym[T]) => s.lt(num(s, 1), num(s, 2)))
  }

  test("a let of a constant names nothing; one that stays lets its body know the parts it may write") {
    same([T[_]] => (s: Sym[T]) => s.let(num(s, 3), Bound[BigInt]("x", big))(x => s.add(x, x)),
      [T[_]] => (s: Sym[T]) => s.add(num(s, 3), num(s, 3)))
    same([T[_]] => (s: Sym[T]) =>
        s.let(s.pair(s.add(num(s, 1), num(s, 2)), num(s, 5)), Bound[(BigInt, BigInt)]("p", pairOf))(p =>
          s.add(s.field(p, Selector.first[BigInt, BigInt](big)), s.field(p, Selector.second[BigInt, BigInt](big)))),
      [T[_]] => (s: Sym[T]) =>
        s.let(s.pair(s.add(num(s, 1), num(s, 2)), num(s, 5)), Bound[(BigInt, BigInt)]("p", pairOf))(p =>
          s.add(s.field(p, Selector.first[BigInt, BigInt](big)), num(s, 5))))
  }

  test("a list joined with none is itself") {
    same([T[_]] => (s: Sym[T]) => s.append(s.nil[BigInt](big), s.cons(num(s, 1), s.nil[BigInt](big))),
      [T[_]] => (s: Sym[T]) => s.cons(num(s, 1), s.nil[BigInt](big)))
  }

  private val pairOf = frflow.core.ty.Ty.TupleOf(List(big, big))
