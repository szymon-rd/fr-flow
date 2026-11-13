package frflow.eval.term

import frflow.core.Lang
import frflow.core.code.Values
import frflow.core.expr.{LawSeeds, Terms, Tm, Value}
import frflow.core.term.{Bound, Selector}
import frflow.core.term.interpret.ToExpr
import frflow.core.term.language.{Final, Sym}
import frflow.core.term.optimize.{Decided, Inlined, Joined, Optimized, Projected}
import frflow.core.ty.Ty
import frflow.eval.Env
import frflow.proof.prover.laws.MoreTerms

/** The optimizations by `fwd` and `bwd` (`core.term.optimize`). Each pass, and their chain, leaves a term its
  * value, on the terms the laws generate; each takes out what it is for and nothing else; and a term none of them
  * is for comes out as it went in.
  */
class OptimizedSuite extends munit.FunSuite:
  private val big = Lang.big
  private val pairOf = Ty.TupleOf(List(big, big))
  private def num[T[_]](s: Sym[T], n: Int): T[BigInt] = s.lit(BigInt(n), Value.Num(n), big)
  private def first[T[_]](s: Sym[T], p: T[(BigInt, BigInt)]) = s.field(p, Selector.first[BigInt, BigInt](big))
  private def second[T[_]](s: Sym[T], p: T[(BigInt, BigInt)]) = s.field(p, Selector.second[BigInt, BigInt](big))
  /** A pass, at every type. */
  private type Pass = [A] => Final[A] => Final[A]
  private val projected: Pass = [A] => (t: Final[A]) => Projected.of(t)
  private val decided: Pass = [A] => (t: Final[A]) => Decided.of(t)
  private val joined: Pass = [A] => (t: Final[A]) => Joined.of(t)
  private val inlined: Pass = [A] => (t: Final[A]) => Inlined.of(t)
  private val chain: Pass = [A] => (t: Final[A]) => Optimized.of(t)
  private val passes: List[(String, Pass)] = List("Projected" -> projected, "Decided" -> decided,
    "Joined" -> joined, "Inlined" -> inlined, "the chain" -> chain)
  private def gives[A](pass: Pass)(given_ : Final[A], expected: Final[A]): Unit =
    assertEquals(ToExpr.of(pass(given_)), ToExpr.of(expected))

  private val generated: List[Final[Boolean]] =
    LawSeeds(600).flatMap(seed => List(Tm.closed(Terms(seed).bool(3, 0)), MoreTerms(seed).formula)).map(Closed.of)

  test("each pass, and their chain, leaves a term the value it had, on the terms the laws generate") {
    val env = Env.of(Values.none)
    val valued = generated.filter(t => Evaluate.of(t)(env).isRight)
    assert(valued.size >= 700, valued.size)
    assertEquals(passes.map((name, pass) =>
      name -> valued.count(t => Evaluate.of(pass(t))(env) != Evaluate.of(t)(env))).filter(_._2 > 0), Nil)
  }

  test("a term no pass is for comes out as it went in: bwd of fwd is the term") {
    val plain: Final[Boolean] = [T[_]] => (s: Sym[T]) => s.lt(s.add(num(s, 1), num(s, 2)), num(s, 4))
    passes.foreach((name, pass) => assertEquals(ToExpr.of(pass(plain)), ToExpr.of(plain), name))
  }

  test("Projected: a part of a pair just made is that part") {
    gives[BigInt](projected)([T[_]] => (s: Sym[T]) => second(s, s.pair(num(s, 1), num(s, 2))),
      [T[_]] => (s: Sym[T]) => num(s, 2))
  }

  test("Decided: an if on a truth value written out is its branch, a connective with one its other side") {
    gives[BigInt](decided)([T[_]] => (s: Sym[T]) => s.cond(s.not(s.bool(false)), num(s, 1), num(s, 2)),
      [T[_]] => (s: Sym[T]) => num(s, 1))
    gives[Boolean](decided)([T[_]] => (s: Sym[T]) => s.and(s.bool(true), s.lt(num(s, 1), num(s, 2))),
      [T[_]] => (s: Sym[T]) => s.lt(num(s, 1), num(s, 2)))
    gives[Boolean](decided)([T[_]] => (s: Sym[T]) => s.implies(s.lt(num(s, 1), num(s, 2)), s.bool(true)),
      [T[_]] => (s: Sym[T]) => s.bool(true))
  }

  test("Joined: a list joined with none is itself") {
    gives[List[BigInt]](joined)(
      [T[_]] => (s: Sym[T]) => s.append(s.nil[BigInt](big), s.cons(num(s, 1), s.nil[BigInt](big))),
      [T[_]] => (s: Sym[T]) => s.cons(num(s, 1), s.nil[BigInt](big)))
  }

  test("Inlined: a let of a constant names nothing; a let of what is computed stays") {
    gives[BigInt](inlined)([T[_]] => (s: Sym[T]) => s.let(num(s, 3), Bound[BigInt]("x", big))(x => s.add(x, x)),
      [T[_]] => (s: Sym[T]) => s.add(num(s, 3), num(s, 3)))
    val computed: Final[BigInt] = [T[_]] => (s: Sym[T]) =>
      s.let(s.add(num(s, 1), num(s, 2)), Bound[BigInt]("x", big))(x => s.add(x, x))
    gives[BigInt](inlined)(computed, computed)
  }

  test("the chain: a let that named a pair of constants, read as the pair, has its part read after it") {
    val named: Final[BigInt] = [T[_]] => (s: Sym[T]) =>
      s.let(s.pair(num(s, 1), num(s, 2)), Bound[(BigInt, BigInt)]("p", pairOf))(p => s.add(first(s, p), second(s, p)))
    gives[BigInt](chain)(named, [T[_]] => (s: Sym[T]) => s.add(num(s, 1), num(s, 2)))
    assertNotEquals(ToExpr.of(Inlined.of(named)), ToExpr.of(Optimized.of(named)))
  }
