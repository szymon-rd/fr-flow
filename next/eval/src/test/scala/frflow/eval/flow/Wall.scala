package frflow.eval.flow

import cats.effect.{IO, Ref}

/** A clock as plain Scala, a virtual one (as Cats Effect's `TestControl`): the time now, in seconds, a wait moving it
  * on by exactly its seconds, and the world's own step between runs (`elapse`, `TestControl.advance`), neither ever
  * by less than none (`Wall.at`); or one whose every call throws (`Wall.stopped`, a service that is down).
  */
trait Wall:
  def now: IO[BigInt]
  def sleep(seconds: BigInt): IO[Unit]
  def elapse(seconds: BigInt): IO[Unit]
  /** The time, read back. */
  def time: IO[BigInt]

object Wall:
  def at(start: BigInt): IO[Wall] = IO.ref(start).map(ticking)

  def ticking(t: Ref[IO, BigInt]): Wall = new Wall:
    def now: IO[BigInt] = t.get
    def sleep(seconds: BigInt): IO[Unit] = t.update(_ + seconds.max(0))
    def elapse(seconds: BigInt): IO[Unit] = t.update(_ + seconds.max(0))
    def time: IO[BigInt] = t.get

  def stopped(broken: Throwable): Wall = new Wall:
    def now: IO[BigInt] = IO.raiseError(broken)
    def sleep(seconds: BigInt): IO[Unit] = IO.raiseError(broken)
    def elapse(seconds: BigInt): IO[Unit] = IO.raiseError(broken)
    def time: IO[BigInt] = IO.raiseError(broken)
