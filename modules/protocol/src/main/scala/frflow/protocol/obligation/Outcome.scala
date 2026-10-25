package frflow.protocol
package obligation

import io.circe.Codec

final case class Outcome(status: ObligationStatus, detail: String = "") derives Codec.AsObject

object Outcome:
  val unchecked: Outcome = Outcome(ObligationStatus.Unchecked, "not checked yet")
  def of(r: Result): Outcome = Outcome(r.status, r.detail)
