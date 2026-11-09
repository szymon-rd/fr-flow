package sharing.time

import cats.effect.{IO, Ref}
import frflow.*

/** The service's run: when it started, and how often housekeeping keeps up with it. Where the service is at a moment
  * is the World's (owner §45 D, §47): what the store, the mail server and the clock hold, and when housekeeping last
  * ran.
  */
object Run:
  val startedAt = Definition[BigInt]("when the service started, in seconds")
  val housekeepingWithin = Definition[BigInt]("the longest the service goes without a run of housekeeping, in seconds")

  val housekeepingPeriod = Node.claim("The service never goes more than two minutes without a run of housekeeping.")(
    housekeepingWithin === 120)

/** When housekeeping last ran, in memory: tested against `housekeptModel`. */
final class Housekept private (at: Ref[IO, BigInt]):
  def ranAt(t: BigInt): IO[Unit] = at.set(t)
  def last: IO[BigInt] = at.get

object Housekept:
  def at(t: BigInt): IO[Housekept] = Ref[IO].of(t).map(Housekept(_))
