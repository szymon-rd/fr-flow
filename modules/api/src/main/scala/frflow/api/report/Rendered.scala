package frflow.api
package report

import io.circe.Codec

final case class Rendered(changed: List[String], snapshot: String) derives Codec.AsObject
