package frflow.protocol
package obligation

import io.circe.Codec
import java.time.Instant

/** The outcome of checking one node, against the hash of what the check depends on. */
final case class NodeCheck(hash: Hash, status: CheckStatus, obligations: List[Result], messages: List[String],
    axioms: List[String], at: Instant, hint: Option[String] = None) derives Codec.AsObject:
  def result(name: ObligationName): Option[Result] = obligations.find(_.name == name)
