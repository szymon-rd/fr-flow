package frflow.dsl.flow

import frflow.core.term.{Bound, Program, Sym, World}
import frflow.core.ty.Ty
import frflow.dsl.build.Source
import frflow.dsl.term.{LeanType, Notes, Term}

/** A run of a program from a world, as a claim about a program states it (`Worlds.runs`): what a run that succeeds
  * gives, `runExpiry(now).from(before) { (result, after) => … }` (to which the failing side may be added, `Ran`), or
  * what one that fails gives alone, `.failing { (error: Term[E], after) => … }`. The outcome and the world after are
  * bound by host functions, their names read at compile time.
  */
final class RunFrom[R](run: Term[Program[R]], before: Term[World])(using r: LeanType[R]):
  inline def apply(inline post: (Term[R], Term[World]) => Term[Boolean]): Ran[R] =
    Ran(run, before, RunFrom.runs(run, before, Source.of(post).params)(post))
  inline def failing[E: LeanType](inline post: (Term[E], Term[World]) => Term[Boolean]): Term[Boolean] =
    RunFrom.fails(run, before, Source.of(post).params)(post)

object RunFrom:
  def runs[R: LeanType](run: Term[Program[R]], before: Term[World], hints: List[String])(
      post: (Term[R], Term[World]) => Term[Boolean]): Term[Boolean] =
    val (o, w) = bounds[R](hints, "result")
    Term.noted(Notes.of(LeanType[R].declares))([T[_]] => (s: Sym[T]) =>
      s.runs(run.run(s), before.run(s), o, w)((x, y) => post(Term.bound(s, x), Term.bound(s, y)).run(s)))

  def fails[R, E: LeanType](run: Term[Program[R]], before: Term[World], hints: List[String])(
      post: (Term[E], Term[World]) => Term[Boolean]): Term[Boolean] =
    val (e, w) = bounds[E](hints, "error")
    Term.noted(Notes.of(LeanType[E].declares))([T[_]] => (s: Sym[T]) =>
      s.fails(run.run(s), before.run(s), e, w)((x, y) => post(Term.bound(s, x), Term.bound(s, y)).run(s)))

  /** The binders' names: the developer's, or, for one written `_`, what it is. */
  private def bounds[O: LeanType](hints: List[String], outcome: String): (Bound[O], Bound[World]) =
    def named(i: Int, otherwise: String) = hints.lift(i).filterNot(_.startsWith("_")).getOrElse(otherwise)
    (Bound[O](named(0, outcome), LeanType[O].ty), Bound[World](named(1, "after"), Ty.World))
