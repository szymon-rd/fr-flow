package frflow.api
package details

import io.circe.Codec

final case class FieldChange(field: String, lines: List[DiffLine]) derives Codec.AsObject
