package frflow.core.name

/** A domain type's Lean name: an opaque type (`User`) or a case class or enum (`Model.Session`). */
opaque type TypeName = String

object TypeName extends Label[TypeName]
