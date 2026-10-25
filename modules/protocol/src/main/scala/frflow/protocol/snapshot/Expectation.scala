package frflow.protocol
package snapshot

import io.circe.Codec

final case class Expectation(statement: String, source: String, status: ObligationStatus, detail: String) derives Codec.AsObject
