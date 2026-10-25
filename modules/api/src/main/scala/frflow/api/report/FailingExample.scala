package frflow.api
package report

import io.circe.Codec

final case class FailingExample(example: String, verdict: String) derives Codec.AsObject
