package frflow.core.term.algebra

import frflow.core.expr.OutsideFact
import frflow.core.name.ModelName
import frflow.core.term.{Bound, Program, World}
import frflow.core.ty.Ty

/** The models' worlds, and runs of a program between them: what a claim about a program says. A run's outcome is
  * bound by a host function (higher-order abstract syntax, LNCS 7470 §3.2), as a quantifier's variable is: `runs`
  * binds the result and the world after a run that succeeds, `fails` the error and the world after one that fails.
  */
trait Worlds[T[_]]:
  def part[S](w: T[World], model: ModelName, ty: Ty): T[S]
  def runs[R](p: T[Program[R]], before: T[World], result: Bound[R], after: Bound[World])(
      post: (T[R], T[World]) => T[Boolean]): T[Boolean]
  def fails[R, E](p: T[Program[R]], before: T[World], error: Bound[E], after: Bound[World])(
      post: (T[E], T[World]) => T[Boolean]): T[Boolean]
  /** Every model's state in `after` is its state in `before` (`.failsChangingNothing`): the worlds' faults, which
    * the calls of a failing model's operations take, are no model's.
    */
  def unchanged(after: T[World], before: T[World]): T[Boolean]
  /** A fact about the world outside the code (an assumption's formula): what Lean's model of the world is built on. */
  def outside(fact: OutsideFact): T[Boolean]
