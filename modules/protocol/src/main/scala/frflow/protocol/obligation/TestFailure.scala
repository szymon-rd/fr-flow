package frflow.protocol
package obligation

import io.circe.Codec

/** A failing case, shrunk: `shown`, its inputs by name (and the world it ran in); `why`, what the code returned and why it
  * fails; the seed, index and size make it again.
  */
final case class TestFailure(shown: String, why: String, seed: Long, index: Int, size: Int) derives Codec.AsObject:
  /** The case and why it fails, on one line. */
  def line: String = if shown.isEmpty then why else s"$shown: $why"
