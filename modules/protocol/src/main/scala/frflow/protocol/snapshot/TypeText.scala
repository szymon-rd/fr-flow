package frflow.protocol
package snapshot

import io.circe.Codec

final case class TypeText(name: String, lean: String) derives Codec.AsObject
