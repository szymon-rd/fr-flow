package frflow

/** What a contract on an operation of type `F` is written with, by how many inputs the operation takes (0 to 6): the
  * builders (`Node.contract`, `checkedBy`, `keeps`, `implementProven`, `run`) take the lambda this gives, so a call keeps
  * its natural form at any arity, `(by, doc, withWhom, result) => …`. A flow's operation (`(A, B) => Flow[R]`) adds the
  * worlds before and after its run: `(a, b, result, before, after) => …`.
  */
trait Sig[F]:
  /** A lambda over a call: its inputs, then its result; a flow's, then the worlds before and after. */
  type Lam[O] <: AnyRef
  /** A flow's code: its steps, from its inputs as terms. An operation's code is `F` itself (none here). */
  type Code
  /** A flow run in `G`: a function of its inputs. */
  type Runs[G[_]]

// An operation's: tried after a flow's, so `A => Flow[R]` is a flow's operation, not an operation giving a flow.
trait OperationSigs:
  given op0[R]: Sig[() => R] with
    type Lam[O] = Term[R] => O
    type Code = Nothing
    type Runs[G[_]] = Nothing
  given op1[A, R]: Sig[A => R] with
    type Lam[O] = (Term[A], Term[R]) => O
    type Code = Nothing
    type Runs[G[_]] = Nothing
  given op2[A, B, R]: Sig[(A, B) => R] with
    type Lam[O] = (Term[A], Term[B], Term[R]) => O
    type Code = Nothing
    type Runs[G[_]] = Nothing
  given op3[A, B, C, R]: Sig[(A, B, C) => R] with
    type Lam[O] = (Term[A], Term[B], Term[C], Term[R]) => O
    type Code = Nothing
    type Runs[G[_]] = Nothing
  given op4[A, B, C, D, R]: Sig[(A, B, C, D) => R] with
    type Lam[O] = (Term[A], Term[B], Term[C], Term[D], Term[R]) => O
    type Code = Nothing
    type Runs[G[_]] = Nothing
  given op5[A, B, C, D, E, R]: Sig[(A, B, C, D, E) => R] with
    type Lam[O] = (Term[A], Term[B], Term[C], Term[D], Term[E], Term[R]) => O
    type Code = Nothing
    type Runs[G[_]] = Nothing
  given op6[A, B, C, D, E, X, R]: Sig[(A, B, C, D, E, X) => R] with
    type Lam[O] = (Term[A], Term[B], Term[C], Term[D], Term[E], Term[X], Term[R]) => O
    type Code = Nothing
    type Runs[G[_]] = Nothing

object Sig extends OperationSigs:
  private type W = Term[World]
  given flow0[R]: Sig[() => Flow[R]] with
    type Lam[O] = (Term[R], W, W) => O
    type Code = () => Flow[R]
    type Runs[G[_]] = () => G[R]
  given flow1[A, R]: Sig[A => Flow[R]] with
    type Lam[O] = (Term[A], Term[R], W, W) => O
    type Code = Term[A] => Flow[R]
    type Runs[G[_]] = A => G[R]
  given flow2[A, B, R]: Sig[(A, B) => Flow[R]] with
    type Lam[O] = (Term[A], Term[B], Term[R], W, W) => O
    type Code = (Term[A], Term[B]) => Flow[R]
    type Runs[G[_]] = (A, B) => G[R]
  given flow3[A, B, C, R]: Sig[(A, B, C) => Flow[R]] with
    type Lam[O] = (Term[A], Term[B], Term[C], Term[R], W, W) => O
    type Code = (Term[A], Term[B], Term[C]) => Flow[R]
    type Runs[G[_]] = (A, B, C) => G[R]
  given flow4[A, B, C, D, R]: Sig[(A, B, C, D) => Flow[R]] with
    type Lam[O] = (Term[A], Term[B], Term[C], Term[D], Term[R], W, W) => O
    type Code = (Term[A], Term[B], Term[C], Term[D]) => Flow[R]
    type Runs[G[_]] = (A, B, C, D) => G[R]
  given flow5[A, B, C, D, E, R]: Sig[(A, B, C, D, E) => Flow[R]] with
    type Lam[O] = (Term[A], Term[B], Term[C], Term[D], Term[E], Term[R], W, W) => O
    type Code = (Term[A], Term[B], Term[C], Term[D], Term[E]) => Flow[R]
    type Runs[G[_]] = (A, B, C, D, E) => G[R]
  given flow6[A, B, C, D, E, X, R]: Sig[(A, B, C, D, E, X) => Flow[R]] with
    type Lam[O] = (Term[A], Term[B], Term[C], Term[D], Term[E], Term[X], Term[R], W, W) => O
    type Code = (Term[A], Term[B], Term[C], Term[D], Term[E], Term[X]) => Flow[R]
    type Runs[G[_]] = (A, B, C, D, E, X) => G[R]
