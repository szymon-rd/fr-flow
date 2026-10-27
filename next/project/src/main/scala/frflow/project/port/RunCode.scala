package frflow.project.port

import cats.Monad
import cats.effect.Sync
import cats.syntax.all.*

/** Running the developer's code (examples, generated cases, searches), which may block or throw: the one effect the
  * programs that run Scala need, so they ask for this rather than `Sync`. Interpreters: blocking on the effect's
  * pool (`make`), and in the effect's own steps (`inline`), for tests. Law, for both: `apply(a)` gives `a`'s value,
  * or raises what `a` throws in `F` when `F` can (the live one).
  */
trait RunCode[F[_]]:
  def apply[A](a: => A): F[A]

object RunCode:
  def make[F[_]: Sync]: RunCode[F] = new RunCode[F]:
    def apply[A](a: => A): F[A] = Sync[F].blocking(a)

  /** In `F`'s own steps, without blocking. */
  def inline[F[_]: Monad]: RunCode[F] = new RunCode[F]:
    def apply[A](a: => A): F[A] = Monad[F].unit.map(_ => a)
