package frflow.protocol
package obligation

import io.circe.Codec

final case class Covered(part: String, held: Int) derives Codec.AsObject
