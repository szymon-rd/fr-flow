package frflow.eval.flow

import cats.effect.kernel.{Async, Sync}
import cats.syntax.all.*

/** How a recorded program's concurrent steps run in Scala: one after the other, as Lean reads them (the models), or
  * at once (the adapters, the interleavings tests).
  */
trait Scheduling[F[_]]:
  def both[A, B](fa: F[A], fb: F[B]): F[(A, B)]
  /** The body on every element, at most `limit` at once when there is one, the results in the list's order. */
  def each[A, B](limit: Option[Int])(xs: List[A])(body: A => F[B]): F[List[B]]
  /** The first of the two to finish, or the reading Lean proves of it (`Prog.Race`: the winner the world says). */
  def race[A, B](fa: F[A], fb: F[B], reading: F[Either[A, B]]): F[Either[A, B]]
  /** `body` with its finalizer, or the reading Lean proves of it (`Prog.Guard`). */
  def guard[A](body: F[A], finalizer: F[Unit], reading: F[A]): F[A]
  def atomically[A](fa: F[A]): F[A]

object Scheduling:
  /** Steps one after the other, as Lean reads them: a pair's left then right, a race read as the world's choice of
    * its winner (`races.leftWins`, the left when the world says nothing) then only the winner's steps, a guarded
    * body read as the finalizer after its result or before its error is raised again.
    */
  def sequential[F[_]](using F: Sync[F]): Scheduling[F] = new Scheduling[F]:
    def both[A, B](fa: F[A], fb: F[B]): F[(A, B)] = fa.product(fb)
    def each[A, B](limit: Option[Int])(xs: List[A])(body: A => F[B]): F[List[B]] = xs.traverse(body)
    def race[A, B](fa: F[A], fb: F[B], reading: F[Either[A, B]]): F[Either[A, B]] = reading
    def guard[A](body: F[A], finalizer: F[Unit], reading: F[A]): F[A] = reading
    def atomically[A](fa: F[A]): F[A] = fa

  /** Branches at once, a race's loser cancelled (its finalizers run), `atomically` under `lock`. */
  def concurrent[F[_]](lock: [A] => F[A] => F[A])(using F: Async[F]): Scheduling[F] = new Scheduling[F]:
    def both[A, B](fa: F[A], fb: F[B]): F[(A, B)] = F.both(fa, fb)
    def each[A, B](limit: Option[Int])(xs: List[A])(body: A => F[B]): F[List[B]] =
      F.parTraverseN(limit.getOrElse(Int.MaxValue))(xs)(body)
    def race[A, B](fa: F[A], fb: F[B], reading: F[Either[A, B]]): F[Either[A, B]] = F.race(fa, fb)
    def guard[A](body: F[A], finalizer: F[Unit], reading: F[A]): F[A] = F.guarantee(body, finalizer)
    def atomically[A](fa: F[A]): F[A] = lock(fa)
