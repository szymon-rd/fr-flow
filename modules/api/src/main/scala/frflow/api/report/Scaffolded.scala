package frflow.api
package report

import frflow.protocol.*
import io.circe.Codec

/** The proof file `scaffold` created or added stubs to, if any. */
final case class Scaffolded(node: NodeId, file: Option[String]) derives Codec.AsObject
