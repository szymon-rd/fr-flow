package frflow.eval.time

import cats.effect.{IO, Ref}

/** When housekeeping last ran, in memory: the plain Scala the time probes test their `ranAt` against. */
final class Housekept private (at: Ref[IO, BigInt]):
  def ranAt(t: BigInt): IO[Unit] = at.set(t)
  def last: IO[BigInt] = at.get

object Housekept:
  def at(t: BigInt): IO[Housekept] = Ref[IO].of(t).map(Housekept(_))
