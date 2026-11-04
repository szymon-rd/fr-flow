package frflow.core.term

import frflow.core.name.{CtorName, TypeName}

/** A case class's or an enum case's constructor, as the curried Scala function `make` (`F = A => B => R`), derived
  * per type. Applied one field at a time with `app`; Lean prints `(Event.Expired now)`.
  */
final case class Constructor[F](data: TypeName, ctor: CtorName, make: F)
