package keycloak

import cats.effect.{IO, Ref}
import cats.effect.std.Queue
import cats.syntax.all.*

/** The requests the HTTP API has received and not yet handed the server, in order: the plain Scala behind `inbox`'s
  * `nextRequest`, which waits for one. What is assumed of it (`drawnTokens`) reads the server's store as well, so its
  * runs on the inbox alone cannot check it: it is trusted.
  */
final class HttpInbox private (queue: Queue[IO, AuthRequest], waiting: Ref[IO, List[AuthRequest]]):
  def next: IO[AuthRequest] = queue.take.flatTap(_ => waiting.update(_.drop(1)))
  /** The next, or `idle` when none waits: the tests' stand-in, whose runs end. */
  def nextOr(idle: AuthRequest): IO[AuthRequest] =
    queue.tryTake.flatMap(_.fold(IO.pure(idle))(q => waiting.update(_.drop(1)).as(q)))
  def offer(q: AuthRequest): IO[Unit] = waiting.update(_ :+ q) *> queue.offer(q)
  /** What is left to hand on. */
  def left: IO[List[AuthRequest]] = waiting.get

object HttpInbox:
  def holding(qs: List[AuthRequest]): IO[HttpInbox] =
    for
      q <- Queue.unbounded[IO, AuthRequest]
      w <- Ref[IO].of(List.empty[AuthRequest])
      i  = HttpInbox(q, w)
      _ <- qs.traverse_(i.offer)
    yield i
