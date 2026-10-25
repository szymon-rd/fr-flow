package frflow.protocol
package snapshot

import io.circe.Codec

final case class DefText(name: String, source: String) derives Codec.AsObject
