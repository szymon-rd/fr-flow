package frflow.agent.conversation

import io.circe.Codec
import java.time.Instant

/** What the developer told the agent in chat, word for word, and when; or their reply to a question. */
final case class Said(text: String, at: Instant) derives Codec.AsObject
