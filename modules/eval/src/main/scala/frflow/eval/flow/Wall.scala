package frflow.eval.flow

import cats.effect.kernel.{Concurrent, Ref}
import cats.syntax.all.*
import cats.ApplicativeThrow

/** A clock as plain Scala, a virtual one (as Cats Effect's `TestControl`): the time now, in seconds, a wait moving it
  * on by exactly its seconds, and the world's own step between runs (`elapse`, `TestControl.advance`), neither ever
  * by less than none (`Wall.at`); or one whose every call fails (`Wall.stopped`, a service that is down). What a
  * model's tests give FrFlow's clock (`implementTested(Clock.now, Clock.sleep, Clock.elapse)(start = Wall.at[IO],
  * …)`): public, in the facade beside `Clock`, because that line is the model's own main code, which no test-only
  * package reaches (the examples' models are main sources; their tests run in testing's).
  */
trait Wall[F[_]]:
  def now: F[BigInt]
  def sleep(seconds: BigInt): F[Unit]
  def elapse(seconds: BigInt): F[Unit]
  /** The time, read back. */
  def time: F[BigInt]

object Wall:
  def at[F[_]: Concurrent](start: BigInt): F[Wall[F]] = Concurrent[F].ref(start).map(ticking[F])

  def ticking[F[_]](t: Ref[F, BigInt]): Wall[F] = new Wall[F]:
    def now: F[BigInt] = t.get
    def sleep(seconds: BigInt): F[Unit] = t.update(_ + seconds.max(0))
    def elapse(seconds: BigInt): F[Unit] = t.update(_ + seconds.max(0))
    def time: F[BigInt] = t.get

  def stopped[F[_]: ApplicativeThrow](broken: Throwable): Wall[F] = new Wall[F]:
    def now: F[BigInt] = broken.raiseError[F, BigInt]
    def sleep(seconds: BigInt): F[Unit] = broken.raiseError[F, Unit]
    def elapse(seconds: BigInt): F[Unit] = broken.raiseError[F, Unit]
    def time: F[BigInt] = broken.raiseError[F, BigInt]
