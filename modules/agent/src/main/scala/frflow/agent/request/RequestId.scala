package frflow.agent.request

import io.circe.{Codec, Decoder, Encoder}

/** A request's id: `R` and the time it was asked, in base 36 (the next free one when two are asked at once). */
opaque type RequestId = String

object RequestId:
  def apply(s: String): RequestId = s
  extension (r: RequestId) def value: String = r
  given Codec[RequestId] = Codec.from(Decoder.decodeString, Encoder.encodeString)
