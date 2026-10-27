package frflow.testing

import java.util.SplittableRandom

/** Where a run of tests starts (`Settings`); `FRFLOW_SEED` replaces it for one check. Case `i` of a run draws from
  * its own stream, so a failing case replays from `(seed, i)` and its size alone, as today's FrFlow draws them.
  */
final case class Seed(value: Long):
  def forCase(i: Int): SplittableRandom = SplittableRandom(value * 0x9e3779b97f4a7c15L + i)

object Seed:
  /** The size case `i` of `cases` is drawn at: 1 for the first tenth, up to 10 for the last. */
  def sizeOf(i: Int, cases: Int): Int = 1 + i * 10 / cases.max(1)
