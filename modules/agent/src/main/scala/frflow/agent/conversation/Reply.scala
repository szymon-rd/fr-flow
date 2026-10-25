package frflow.agent
package conversation

import io.circe.Codec
import java.time.Instant

/** The developer's reply to a question, as they said it in chat. */
final case class Reply(text: String, at: Instant) derives Codec.AsObject
