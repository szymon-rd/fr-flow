package sharing.notifications

import cats.effect.{IO, Ref}

/** The pool of connections to the mail server, in memory: a count of those in use; tested against `poolModel`. */
final class MemoryPool private (inUse: Ref[IO, BigInt]):
  def take: IO[Unit] = inUse.update(_ + 1)
  def give: IO[Unit] = inUse.update(_ - 1)
  def count: IO[BigInt] = inUse.get

object MemoryPool:
  def holding(n: BigInt): IO[MemoryPool] = Ref[IO].of(n).map(MemoryPool(_))
