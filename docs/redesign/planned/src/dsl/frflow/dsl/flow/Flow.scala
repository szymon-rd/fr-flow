package frflow.dsl.flow

import frflow.core.name.{BoundaryName, OpName}
import frflow.dsl.term.{LeanType, Term}

/** Steps over boundaries as the developer writes them: a higher-order tree. A proven flow elaborates to `Prog`; an
  * implementation's flows (with `Effect` steps) are run as they are by `eval.run.FlowRun`.
  */
enum Flow[A]:
  case Pure(result: Term[A])
  case Call(boundary: BoundaryName, op: OpName, args: List[Term[?]])
  case Bind[X, B](first: Flow[X], next: Term[X] => Flow[B]) extends Flow[B]
  /** A step of the outside world, on the values of the terms it is given: production implementations only. */
  case Effect(args: List[Term[?]], run: List[Any] => A, result: LeanType[A])
  // … Each, EachResult, Fold, Cond, Get, Put, Update, Raise, Catch, Attempt, ParEach, Atomic, as today.

  def flatMap[B](f: Term[A] => Flow[B]): Flow[B] = Bind(this, f)

object Flow:
  def effect[X, A](x: Term[X])(f: X => A)(using a: LeanType[A]): Flow[A] =
    Effect(List(x), vs => f(vs.head.asInstanceOf[X]), a) // the value of `x`, a term of type `X`
  // … `effect` of 0 to 3 terms, `whenA`, `unlessA`, `sequence`, `atomically`, `now`, `sleep`, `every`, as today.
