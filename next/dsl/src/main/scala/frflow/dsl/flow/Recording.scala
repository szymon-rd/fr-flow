package frflow.dsl.flow

import frflow.dsl.term.{LeanType, Term}

/** The proofs' interpreter of programs: each step recorded, nothing run. A program over `Recorded` is read into the
  * `Prog` Lean proves by `ReadRecording`.
  */
object Recording:
  given Flow[Recorded] with
    def pure[A](a: A): Recorded[A] = Recorded.Pure(a)
    def flatMap[A, B](fa: Recorded[A])(f: A => Recorded[B]): Recorded[B] = Recorded.Bind(fa, f)
    def tailRecM[A, B](a: A)(f: A => Recorded[Either[A, B]]): Recorded[B] =
      flatMap(f(a))(_.fold(tailRecM(_)(f), pure))
    def cond[A](c: Term[Boolean])(ifTrue: => Recorded[A], ifFalse: => Recorded[A]): Recorded[A] =
      Recorded.Cond(c, () => ifTrue, () => ifFalse)
    def each[X: LeanType](xs: Term[List[X]])(body: Term[X] => Recorded[Unit]): Recorded[Unit] =
      Recorded.Each(xs, LeanType[X], body)
    def collect[X: LeanType, B: LeanType](xs: Term[List[X]])(body: Term[X] => Recorded[Term[B]])
        : Recorded[Term[List[B]]] = Recorded.Collect(xs, LeanType[X], body, LeanType[List[B]])
    def fold[X: LeanType, B](xs: Term[List[X]], z: Term[B])(body: (Term[B], Term[X]) => Recorded[Term[B]])
        : Recorded[Term[B]] = Recorded.Fold(xs, z, LeanType[X], body)
    def parCollect[X: LeanType, B: LeanType](xs: Term[List[X]])(body: Term[X] => Recorded[Term[B]])
        : Recorded[Term[List[B]]] = Recorded.ParCollect(xs, LeanType[X], body, LeanType[List[B]])
    def raise[E, A](error: Term[E]): Recorded[A] = Recorded.Raise(error)
    def handle[E: LeanType, A](fa: Recorded[A])(handler: Term[E] => Recorded[A]): Recorded[A] =
      Recorded.Handle(fa, LeanType[E], handler)
    def guarantee[E: LeanType, A](fa: Recorded[A], finalizer: Recorded[Unit]): Recorded[A] =
      Recorded.Guard(fa, LeanType[E], finalizer)
    def race[A: LeanType, B: LeanType](fa: Recorded[Term[A]], fb: Recorded[Term[B]]): Recorded[Term[Either[A, B]]] =
      Recorded.Race(fa, fb, LeanType[Either[A, B]])
    def parTupled[A: LeanType, B: LeanType](fa: Recorded[Term[A]], fb: Recorded[Term[B]]): Recorded[Term[(A, B)]] =
      Recorded.Par(fa, fb, LeanType[(A, B)])
    def atomically[A](fa: Recorded[A]): Recorded[A] = Recorded.Atomic(fa)
