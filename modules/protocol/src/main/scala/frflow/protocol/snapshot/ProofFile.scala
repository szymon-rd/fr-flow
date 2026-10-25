package frflow.protocol
package snapshot

import io.circe.Codec

final case class ProofFile(file: String, source: String) derives Codec.AsObject
