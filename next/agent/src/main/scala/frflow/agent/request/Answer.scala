package frflow.agent.request

import io.circe.Codec
import java.time.Instant

/** The agent's answer to a request: what it did or why not, and when. */
final case class Answer(text: String, at: Instant) derives Codec.AsObject
