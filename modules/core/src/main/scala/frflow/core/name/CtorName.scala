package frflow.core.name

/** A constructor of a domain type: an enum's case (`ById`), or `mk` for a case class. */
opaque type CtorName = String

object CtorName extends Label[CtorName]
