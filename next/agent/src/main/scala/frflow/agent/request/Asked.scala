package frflow.agent.request

import io.circe.Codec
import java.time.Instant

/** Who asked, when, and the node's version as they saw it (none for a request on the whole idea). */
final case class Asked(by: String, at: Instant, seen: Option[String]) derives Codec.AsObject
