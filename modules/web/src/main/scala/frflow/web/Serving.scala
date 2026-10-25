package frflow.web

import io.circe.Codec

/** Who decides on the page, and whether the model's sources changed since `serve` started: then nothing is decided. */
final case class Serving(developer: String, modelChanged: Boolean) derives Codec.AsObject
