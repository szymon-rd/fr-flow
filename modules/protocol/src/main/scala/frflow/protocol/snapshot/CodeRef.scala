package frflow.protocol
package snapshot

import io.circe.Codec

final case class CodeRef(files: List[String], fingerprint: Fingerprint) derives Codec.AsObject
