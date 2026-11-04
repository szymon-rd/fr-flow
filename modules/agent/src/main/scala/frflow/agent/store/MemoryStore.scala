package frflow.agent.store

import cats.effect.{Concurrent, Ref}
import cats.effect.std.Mutex
import cats.syntax.all.*

/** A store in memory, starting at `initial`: the agent layer's suites run without files. */
object MemoryStore:
  def apply[F[_]: Concurrent, A](initial: A): F[Store[F, A]] =
    (Ref.of[F, A](initial), Mutex[F]).mapN((ref, mutex) => new Store[F, A]:
      def load: F[A] = ref.get
      def update[E, B](f: A => Either[E, (A, B)]): F[Either[E, B]] =
        mutex.lock.surround(ref.get.flatMap(a => f(a).traverse((next, b) => ref.set(next).as(b)))))
