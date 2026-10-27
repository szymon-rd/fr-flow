package frflow.dsl.flow

import frflow.core.term.{Program, Sym, World}
import frflow.dsl.build.Source
import frflow.dsl.term.{LeanType, Term}

/** What a run that succeeds gives, `op(a).from(before) { (result, after) => … }`, to which what a run that fails gives
  * may be added, `.failing { (error: Term[E], after) => … }`: one run, both outcomes, as a match states its cases. A
  * claim's formula so written is read as its post and its failure clause (`spec.CallForms`).
  */
final class Ran[R](run: Term[Program[R]], before: Term[World], succeeds: Term[Boolean])
    extends Term[Boolean](succeeds.run):
  inline def failing[E: LeanType](inline post: (Term[E], Term[World]) => Term[Boolean]): Term[Boolean] =
    Ran.both(succeeds, RunFrom.fails(run, before, Source.of(post).params)(post))
  /** A run that fails with an `E` changes nothing: the world after it is the world before. */
  def failsChangingNothing[E: LeanType]: Term[Boolean] =
    Ran.both(succeeds, RunFrom.fails[R, E](run, before, List("_", "after"))((_, after) =>
      Term.both(after, before)([T[_]] => (s: Sym[T]) => s.eq[World])))

object Ran:
  def both(succeeds: Term[Boolean], fails: Term[Boolean]): Term[Boolean] =
    Term.both(succeeds, fails)([T[_]] => (s: Sym[T]) => s.and)
