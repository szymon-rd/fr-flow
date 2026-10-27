package frflow.agent.request

import io.circe.{Codec, Decoder, Encoder}

/** Where a request stands: asked and open, answered by the agent (for the developer to read), or closed by the
  * developer.
  */
enum RequestStatus:
  case Open, Answered, Closed

  def word: String = toString.toLowerCase

object RequestStatus:
  given Codec[RequestStatus] = Codec.from(
    Decoder.decodeString.emap(s => values.find(_.word == s).toRight(s"no request status $s")),
    Encoder.encodeString.contramap(_.word))
