package frflow.dsl.flow

/** FrFlow's own boundary: the time in seconds, and waiting. Its model is a counter only sleeps move. */
trait Clock[F[_], T[_]]:
  def now: F[T[BigInt]]
  def sleep(seconds: T[BigInt]): F[Unit]

object Clock:
  given BoundaryOps[Clock] = ClockOps
