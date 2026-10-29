package frflow.eval.flow

import cats.effect.{IO, Ref}

/** A clock as plain Scala: the time now, in seconds, and a wait moving it on (`Wall.at`), or one whose every call
  * throws (`Wall.stopped`, a service that is down).
  */
trait Wall:
  def now: IO[BigInt]
  def sleep(seconds: BigInt): IO[Unit]
  /** The time, read back. */
  def time: IO[BigInt]

object Wall:
  def at(start: BigInt): IO[Wall] = IO.ref(start).map(ticking)

  def ticking(t: Ref[IO, BigInt]): Wall = new Wall:
    def now: IO[BigInt] = t.get
    def sleep(seconds: BigInt): IO[Unit] = t.update(_ + seconds)
    def time: IO[BigInt] = t.get

  def stopped(broken: Throwable): Wall = new Wall:
    def now: IO[BigInt] = IO.raiseError(broken)
    def sleep(seconds: BigInt): IO[Unit] = IO.raiseError(broken)
    def time: IO[BigInt] = IO.raiseError(broken)
