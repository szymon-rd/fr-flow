package frflow.testing

import frflow.core.name.SymbolName
import frflow.core.term.*
import frflow.core.term.interpret.Forward
import frflow.core.ty.Ty
import frflow.eval.EvalError
import frflow.eval.term.{Evaluate, Run}
import frflow.testing.report.{Position, Reach, Target}

/** The evaluator, watched: each part of a formula a test must reach (`Reach`) is declared when the term is built
  * (`declared`) and said when a run reaches it (`reached`). A part's position is its place among the parts built at
  * its level, under the binder above it, so the parts a binder's body builds for each element share their positions.
  * Surveying, each body is also built once on a placeholder, so every part is declared before anything runs.
  * Its one state is the place being built, local to one watched build and run.
  */
final class Watching(declared: Target => Unit, reached: Target => Unit, surveying: Boolean)
    extends Forward[Run, Run]:
  protected def base: Sym[Run] = Evaluate
  protected def fwd[A](t: Run[A]): Run[A] = t
  protected def bwd[A](u: Run[A]): Run[A] = u

  private var above: List[Int] = Nil
  private var built: Int = 0

  override def implies(a: Run[Boolean], b: Run[Boolean]): Run[Boolean] =
    val t = target(place(), Reach.Premise)
    base.implies(when(a, t, true), b)

  override def or(a: Run[Boolean], b: Run[Boolean]): Run[Boolean] =
    val at = place()
    base.or(when(a, target(at, Reach.Side(0)), true), when(b, target(at, Reach.Side(1)), true))

  override def cond[A](c: Run[Boolean], t: Run[A], e: Run[A]): Run[A] =
    val at = place()
    val (yes, no) = (target(at, Reach.Branch(true)), target(at, Reach.Branch(false)))
    base.cond(env => c(env).map { v => reached(if v then yes else no); v }, t, e)

  override def all[A](xs: Run[List[A]], x: Bound[A])(p: Run[A] => Run[Boolean]): Run[Boolean] =
    val t = target(place(), Reach.NonEmpty)
    base.all(nonEmpty(xs, t, _.nonEmpty), x)(body(p))

  override def any[A](xs: Run[List[A]], x: Bound[A])(p: Run[A] => Run[Boolean]): Run[Boolean] =
    val t = target(place(), Reach.NonEmpty)
    base.any(nonEmpty(xs, t, _.nonEmpty), x)(body(p))

  override def optionAll[A](o: Run[Option[A]], x: Bound[A])(p: Run[A] => Run[Boolean]): Run[Boolean] =
    val t = target(place(), Reach.NonEmpty)
    base.optionAll(nonEmpty(o, t, _.isDefined), x)(body(p))

  override def optionAny[A](o: Run[Option[A]], x: Bound[A])(p: Run[A] => Run[Boolean]): Run[Boolean] =
    val t = target(place(), Reach.NonEmpty)
    base.optionAny(nonEmpty(o, t, _.isDefined), x)(body(p))

  override def foldOption[A, R](o: Run[Option[A]], ifNone: Run[R], x: Bound[A])(ifSome: Run[A] => Run[R]): Run[R] =
    val at = place()
    val (none, some) = (target(at, Reach.Arm(0)), target(at, Reach.Arm(1)))
    base.foldOption(o, taken(none, ifNone), x)(body(v => taken(some, ifSome(v))))

  override def foldEither[E, A, R](v: Run[Either[E, A]], e: Bound[E], a: Bound[A])(l: Run[E] => Run[R],
      r: Run[A] => Run[R]): Run[R] =
    val at = place()
    val (left, right) = (target(at, Reach.Arm(0)), target(at, Reach.Arm(1)))
    base.foldEither(v, e, a)(body(x => taken(left, l(x))), body(x => taken(right, r(x))))

  override def cases[S, R](s: Run[S], arms: List[When[Run, S, ?, R]], ty: Ty): Run[R] =
    val at = place()
    base.cases(s, arms.zipWithIndex.map((w, i) => arm(w, target(at, Reach.Arm(i)))), ty)

  override def pairwise[A](xs: Run[List[A]], x: Bound[A], y: Bound[A])(p: (Run[A], Run[A]) => Run[Boolean])
      : Run[Boolean] =
    val scoped = body2(p)
    base.pairwise(xs, x, y)(scoped)

  override def foldLeft[A, B](xs: Run[List[A]], z: Run[B], acc: Bound[B], x: Bound[A])(f: (Run[B], Run[A]) => Run[B])
      : Run[B] =
    val scoped = body2(f)
    base.foldLeft(xs, z, acc, x)(scoped)

  override def runs[R](p: Run[Program[R]], before: Run[World], result: Bound[R], after: Bound[World])(
      post: (Run[R], Run[World]) => Run[Boolean]): Run[Boolean] =
    val scoped = body2(post)
    base.runs(p, before, result, after)(scoped)

  override def fails[R, E](p: Run[Program[R]], before: Run[World], error: Bound[E], after: Bound[World])(
      post: (Run[E], Run[World]) => Run[Boolean]): Run[Boolean] =
    val scoped = body2(post)
    base.fails(p, before, error, after)(scoped)

  /** A binder's body, built under the binder's place, for each value it is run on (surveyed once on a placeholder). */
  override protected def body[A, B](p: Run[A] => Run[B]): Run[A] => Run[B] =
    val here = place()
    if surveying then { val _ = inside(here)(p(Watching.placeholder)) }
    v => inside(here)(p(v))

  private def body2[A, B, C](p: (Run[A], Run[B]) => Run[C]): (Run[A], Run[B]) => Run[C] =
    val here = place()
    if surveying then { val _ = inside(here)(p(Watching.placeholder, Watching.placeholder)) }
    (a, b) => inside(here)(p(a, b))

  private def arm[S, C, R](w: When[Run, S, C, R], t: Target): When[Run, S, C, R] =
    When(w.c, w.x, body(v => taken(t, w.body(v))))

  private def place(): Position =
    val p = Position((built :: above).reverse)
    built += 1
    p

  private def inside[A](at: Position)(build: => A): A =
    val (outer, count) = (above, built)
    above = at.path.reverse
    built = 0
    try build
    finally { above = outer; built = count }

  private def target(at: Position, r: Reach): Target =
    val t = Target(at, r)
    declared(t)
    t

  private def when(a: Run[Boolean], t: Target, value: Boolean): Run[Boolean] =
    env => a(env).map { v => if v == value then reached(t); v }

  private def nonEmpty[C](xs: Run[C], t: Target, holds: C => Boolean): Run[C] =
    env => xs(env).map { c => if holds(c) then reached(t); c }

  private def taken[R](t: Target, r: Run[R]): Run[R] = env => { reached(t); r(env) }

object Watching:
  /** What a body is built on to survey it: never run. */
  private def placeholder[A]: Run[A] = _ => Left(EvalError.Unbound(SymbolName("survey")))
