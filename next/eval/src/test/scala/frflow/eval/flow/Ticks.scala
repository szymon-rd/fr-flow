package frflow.eval.flow

import frflow.*

/** The clock's model: the time now, moved on by a sleep only. */
final class Ticks[F[_]: Flow](state: Model[F, BigInt]) extends Clock[F, Term]:
  def now: F[Term[BigInt]] = state.get
  def sleep(seconds: Term[BigInt]): F[Unit] = state.get.flatMap(t => state.set(t + seconds))
