package frflow.dsl.flow

import frflow.core.term.{Program, World}
import frflow.dsl.term.{LeanType, Term}
import frflow.dsl.vocab.Definition

/** The combinators as programs write them: `a.race(b)`, `(a, b).parTupled`, `fa.guarantee[E](fin)`; and, in a flow
  * claim, a run from a world (`runExpiry(now).from(before) { … }`).
  */
object FlowSyntax:
  extension [R: LeanType](run: Term[Program[R]])
    def from(before: Term[World]): RunFrom[R] = RunFrom(run, before)

  extension [F[_], A](fa: F[Term[A]])(using f: Flow[F], a: LeanType[A])
    def race[B: LeanType](fb: F[Term[B]]): F[Term[Either[A, B]]] = f.race(fa, fb)
    def timeout(now: Definition[Program[BigInt]], seconds: Term[BigInt]): F[Term[Option[A]]] =
      f.timeout(now)(fa, seconds)

  extension [F[_], A](fa: F[A])(using f: Flow[F])
    /** A program's and a model's steps, as `for` reads them. */
    def map[B](g: A => B): F[B] = f.map(fa)(g)
    def flatMap[B](g: A => F[B]): F[B] = f.flatMap(fa)(g)
    def guarantee[E: LeanType](finalizer: F[Unit]): F[A] = f.guarantee[E, A](fa, finalizer)
    def atomically: F[A] = f.atomically(fa)

  extension [F[_], A, B](p: (F[Term[A]], F[Term[B]]))(using f: Flow[F], a: LeanType[A], b: LeanType[B])
    def parTupled: F[Term[(A, B)]] = f.parTupled(p._1, p._2)
