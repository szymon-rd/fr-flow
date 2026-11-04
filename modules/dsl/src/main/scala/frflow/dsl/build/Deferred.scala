package frflow.dsl.build

import cats.{Applicative, Eval}
import cats.data.ValidatedNec
import cats.syntax.all.*

/** A part of a model, built when elaborated: errors accumulate and declarations merge under `mapN`. The one shape a
  * part of a model has before elaboration; terms carry their faults unlocated (`Notes`) until `Elab` places them.
  */
opaque type Deferred[A] = Eval[ValidatedNec[ElabError, (Declarations, A)]]

object Deferred:
  def apply[A](build: => ValidatedNec[ElabError, (Declarations, A)]): Deferred[A] = Eval.later(build)
  def pure[A](a: A): Deferred[A] = Eval.now((Declarations.none, a).validNec)
  def failed[A](at: Site, f: Fault): Deferred[A] = Eval.now(ElabError(at, f).invalidNec)
  extension [A](d: Deferred[A])
    def run: ValidatedNec[ElabError, (Declarations, A)] = d.value
    /** A part built from what an earlier one built (its declarations kept): a statement read off its formula. */
    def andThen[B](f: A => Deferred[B]): Deferred[B] =
      d.map(_.andThen((ds, a) => f(a).value.map((more, b) => (ds |+| more, b))))
  given Applicative[Deferred] =
    Applicative[Eval].compose[[a] =>> ValidatedNec[ElabError, a]].compose[[a] =>> (Declarations, a)]
