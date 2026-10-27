package frflow.dsl.flow

import frflow.core.name.{BoundaryName, ModelName, OpName}
import frflow.dsl.term.{LeanType, Term}

/** A program recorded, one case per step, as `Recording`'s `Flow` builds it: what Lean reads once `Recording.read`
  * has made it `Prog`. Typed as the program's values: a call gives a term of its result.
  */
enum Recorded[A]:
  case Pure(a: A)
  case Call[R](boundary: BoundaryName, op: OpName, args: List[Term[?]], result: LeanType[R]) extends Recorded[Term[R]]
  case Bind[X, B](first: Recorded[X], next: X => Recorded[B]) extends Recorded[B]
  case Cond(c: Term[Boolean], ifTrue: () => Recorded[A], ifFalse: () => Recorded[A])
  case Each[X](xs: Term[List[X]], element: LeanType[X], body: Term[X] => Recorded[Unit]) extends Recorded[Unit]
  case Raise[E, B](error: Term[E]) extends Recorded[B]
  case Handle[E, B](body: Recorded[B], error: LeanType[E], handler: Term[E] => Recorded[B]) extends Recorded[B]
  case Guard[E, B](body: Recorded[B], error: LeanType[E], finalizer: Recorded[Unit]) extends Recorded[B]
  case Race[L, R](left: Recorded[Term[L]], right: Recorded[Term[R]], ty: LeanType[Either[L, R]])
      extends Recorded[Term[Either[L, R]]]
  case Par[L, R](left: Recorded[Term[L]], right: Recorded[Term[R]], ty: LeanType[(L, R)])
      extends Recorded[Term[(L, R)]]
  case Atomic(body: Recorded[A])
  case Read[S](model: ModelName, state: LeanType[S]) extends Recorded[Term[S]]
  case Write[S](model: ModelName, state: Term[S]) extends Recorded[Unit]
  case Collect[X, B](xs: Term[List[X]], element: LeanType[X], body: Term[X] => Recorded[Term[B]],
      ty: LeanType[List[B]]) extends Recorded[Term[List[B]]]
  case Fold[X, B](xs: Term[List[X]], z: Term[B], element: LeanType[X], body: (Term[B], Term[X]) => Recorded[Term[B]])
      extends Recorded[Term[B]]
  case ParCollect[X, B](xs: Term[List[X]], element: LeanType[X], body: Term[X] => Recorded[Term[B]],
      ty: LeanType[List[B]]) extends Recorded[Term[List[B]]]

object Recorded:
  /** The recording `Flow`, found wherever a program is recorded, with no import (`program { … }`). */
  given Flow[Recorded] = Recording.given_Flow_Recorded
