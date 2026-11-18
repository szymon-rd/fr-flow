package frflow.web

import io.circe.Codec

/** Who decides on the page, whether the model's sources changed since `serve` started (then nothing is decided), and
  * whether a supervisor starts the server again on the rebuilt model (then the page waits for it).
  */
final case class Serving(developer: String, modelChanged: Boolean, reloads: Boolean) derives Codec.AsObject
