package frflow.protocol
package snapshot

import io.circe.Codec

final case class ImplProof(name: String, status: ObligationStatus, detail: String) derives Codec.AsObject
