package frflow.api
package details

import frflow.protocol.*
import io.circe.Codec

/** A decided node gone from the model, with its last decision; `renamedTo`: a node in the model that says the same. */
final case class GoneNode(gone: Gone, renamedTo: Option[NodeId]) derives Codec.AsObject
