package frflow.core.ty

import frflow.core.name.CtorName

/** A constructor of a domain type. A case without fields is a singleton (`Search.Everything`). */
final case class Ctor(name: CtorName, fields: List[Field])
