package keycloak

import cats.effect.{IO, Ref}
import cats.effect.std.Queue
import cats.syntax.all.*

/** The requests the HTTP API has received and not yet handed the server, in order: the plain Scala behind `inbox`'s
  * `nextRequest`, which waits for one and is shown the requests the server has handled. A sign-in's token is drawn
  * from a secure random source, 256 bits, as it is received; were one of the handled requests to carry it (a chance
  * neglected), it is drawn again, so what is handed on is fresh against them (`drawnTokens`, tested on the inbox's
  * runs).
  */
final class HttpInbox private (queue: Queue[IO, AuthRequest], waiting: Ref[IO, List[AuthRequest]]):
  def next(handled: List[AuthRequest]): IO[AuthRequest] =
    queue.take.flatTap(_ => waiting.update(_.drop(1))).map(HttpInbox.fresh(handled))
  /** The next, or `idle` when none waits: the tests' stand-in, whose runs end. */
  def nextOr(idle: AuthRequest)(handled: List[AuthRequest]): IO[AuthRequest] =
    queue.tryTake.flatMap(_.fold(IO.pure(idle))(q => waiting.update(_.drop(1)).as(q))).map(HttpInbox.fresh(handled))
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

  /** A sign-in carrying a token one of the handled requests carried, its token drawn again: in the tests, the next
    * after it in a fixed order, so a call from one state gives one request.
    */
  private def fresh(handled: List[AuthRequest])(q: AuthRequest): AuthRequest = q match
    case AuthRequest.SignIn(r, u, h, t) =>
      val used = handled.collect { case AuthRequest.SignIn(_, _, _, x) => x }.toSet
      AuthRequest.SignIn(r, u, h, LazyList.iterate(t)(_ + "'").dropWhile(used).head)
    case other                          => other
