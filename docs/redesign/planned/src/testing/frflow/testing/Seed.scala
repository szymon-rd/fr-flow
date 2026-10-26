package frflow.testing

/** Where a run of tests starts (`TestSettings`); `FRFLOW_SEED` replaces it for one check. Case `i` of a run draws
  * from its own stream, so a failing case replays from `(seed, i)` alone.
  */
final case class Seed(value: Long):
  def forCase(i: Int): java.util.SplittableRandom = java.util.SplittableRandom(value * 0x9e3779b97f4a7c15L + i)
