package frflow.dsl.run

import frflow.core.name.ModelName
import frflow.dsl.term.{LeanType, Term}

/** A program's steps, one case per step, as a `Flow` builds them: what Lean reads once `ReadRecording` has made them
  * `Prog`, and what production folds into its effect (`eval.Running`). Typed as the program's values: a call gives a
  * term of its result, a step giving nothing the unit's term.
  */
enum Recorded[A]:
  case Pure(a: A)
  /** An operation on a state applied, as a step: the term applying it, read as a call of the Definition it applies
    * (`vocab.Called`), its notes declaring the operation and its arguments.
    */
  case Call[R](applied: Term[?], result: LeanType[R]) extends Recorded[Term[R]]
  case Bind[X, B](first: Recorded[X], next: X => Recorded[B]) extends Recorded[B]
  case Cond(c: Term[Boolean], ifTrue: () => Recorded[A], ifFalse: () => Recorded[A])
  case Each[X](xs: Term[List[X]], element: LeanType[X], body: Term[X] => Recorded[?]) extends Recorded[Term[Unit]]
  case Raise[E, B](error: Term[E]) extends Recorded[B]
  case Handle[E, B](body: Recorded[B], error: LeanType[E], handler: Term[E] => Recorded[B]) extends Recorded[B]
  case Guard[E, B](body: Recorded[B], error: LeanType[E], finalizer: Recorded[?]) extends Recorded[B]
  case Race[L, R](left: Recorded[Term[L]], right: Recorded[Term[R]], ty: LeanType[Either[L, R]])
      extends Recorded[Term[Either[L, R]]]
  case Par[L, R](left: Recorded[Term[L]], right: Recorded[Term[R]], ty: LeanType[(L, R)])
      extends Recorded[Term[(L, R)]]
  case Atomic(body: Recorded[A])
  case Read[S](model: ModelName, state: LeanType[S]) extends Recorded[Term[S]]
  case Write[S](model: ModelName, state: Term[S]) extends Recorded[Term[Unit]]
  case Collect[X, B](xs: Term[List[X]], element: LeanType[X], body: Term[X] => Recorded[Term[B]],
      ty: LeanType[List[B]]) extends Recorded[Term[List[B]]]
  case Fold[X, B](xs: Term[List[X]], z: Term[B], element: LeanType[X], body: (Term[B], Term[X]) => Recorded[Term[B]])
      extends Recorded[Term[B]]
  /** At most `limit` at once, when it has one. */
  case ParCollect[X, B](xs: Term[List[X]], element: LeanType[X], body: Term[X] => Recorded[Term[B]],
      ty: LeanType[List[B]], limit: Option[Int]) extends Recorded[Term[List[B]]]
