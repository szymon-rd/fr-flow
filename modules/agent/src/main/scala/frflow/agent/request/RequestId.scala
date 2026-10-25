package frflow.agent
package request

import io.circe.{Codec, Decoder, Encoder}

/** A request's id: `R` and the time it was asked, in base 36. */
opaque type RequestId = String

object RequestId:
  def apply(s: String): RequestId = s
  extension (r: RequestId) def value: String = r
  given Codec[RequestId] = Codec.from(Decoder.decodeString, Encoder.encodeString)
