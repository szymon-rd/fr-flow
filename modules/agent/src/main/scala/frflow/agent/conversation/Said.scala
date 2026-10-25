package frflow.agent
package conversation

import io.circe.Codec
import java.time.Instant

/** What the developer told the agent in chat, word for word. */
final case class Said(text: String, at: Instant) derives Codec.AsObject
