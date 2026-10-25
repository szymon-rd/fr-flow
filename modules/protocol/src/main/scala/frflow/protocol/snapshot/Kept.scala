package frflow.protocol
package snapshot

import io.circe.Codec

final case class Kept(id: NodeId, view: String, rule: String, status: ObligationStatus, detail: String) derives Codec.AsObject
