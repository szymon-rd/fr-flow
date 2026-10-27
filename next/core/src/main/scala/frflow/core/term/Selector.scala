package frflow.core.term

import frflow.core.name.TypeName
import frflow.core.ty.Ty

/** A field of a record type: its name and position, the record's type name, its type, and Scala's own getter and copy
  * of it (derived per type: no interpreter casts).
  */
final case class Selector[R, F](name: String, index: Int, record: TypeName, ty: Ty, get: R => F, set: (R, F) => R)
