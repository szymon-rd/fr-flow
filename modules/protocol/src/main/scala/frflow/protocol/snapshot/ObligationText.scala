package frflow.protocol
package snapshot

import io.circe.Codec

final case class ObligationText(name: String, statement: String, description: String) derives Codec.AsObject
