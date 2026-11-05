package frflow.testing.derive

/** A random stream as a value (SplitMix64): the next number and the stream after it, so a draw is a function of
  * where its stream starts.
  */
final case class Stream(seed: Long):
  def next: (Stream, Long) =
    val s = seed + 0x9e3779b97f4a7c15L
    val z1 = (s ^ (s >>> 30)) * 0xbf58476d1ce4e5b9L
    val z2 = (z1 ^ (z1 >>> 27)) * 0x94d049bb133111ebL
    (Stream(s), z2 ^ (z2 >>> 31))
