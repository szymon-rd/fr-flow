package frflow.agent.store

import cats.effect.{Concurrent, Ref}
import cats.syntax.all.*

/** A store in memory, starting at `initial`, each update one atomic change of a `Ref`: the agent layer's suites run
  * without files.
  */
object MemoryStore:
  def apply[F[_]: Concurrent, A](initial: A): F[Store[F, A]] =
    Ref.of[F, A](initial).map(ref => new Store[F, A]:
      def load: F[A] = ref.get
      def update[E, B](f: A => Either[E, (A, B)]): F[Either[E, B]] =
        ref.modify(a => f(a).fold(e => (a, Left(e)), (next, b) => (next, Right(b)))))
