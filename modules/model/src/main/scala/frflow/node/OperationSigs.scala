package frflow
package node

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
