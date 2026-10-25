package frflow.agent
package panel

import io.circe.Codec

final case class Answering(to: String, text: String) derives Codec.AsObject
