package frflow.protocol
package obligation

import io.circe.Codec

/** A failing case, shrunk: `shown`, its inputs by name (and the world it ran in); `why`, what the code returned and why it
  * fails; the seed, index and size make it again.
  */
final case class TestFailure(shown: String, why: String, seed: Long, index: Int, size: Int) derives Codec.AsObject:
  /** The case and why it fails, on one line. */
  def line: String = if shown.isEmpty then why else s"$shown: $why"

  /** The failure as said of the node `id`'s code: as the code's, or (`contractChanged`) as the contract's change. */
  def said(id: String, contractChanged: Boolean): String =
    if contractChanged then s"the contract changed and its code no longer meets it: ${against(id)}"
    else s"its code fails a generated case: $line"

  /** The case and why it fails, the contract that forbids it being the one that changed. */
  def against(id: String): String =
    val now = why.replace(s"which $id forbids", "which the contract now forbids")
    if shown.isEmpty then now else s"$shown: $now"
