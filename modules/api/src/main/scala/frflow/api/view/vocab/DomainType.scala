package frflow.api.view.vocab

import frflow.core.name.TypeName

/** A domain type, by its name, and what it is made of. */
final case class DomainType(name: TypeName, shape: Shape)
