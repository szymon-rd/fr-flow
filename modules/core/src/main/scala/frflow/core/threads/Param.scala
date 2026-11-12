package frflow.core.threads

/** A named value of a type: a parameter of a definition, a field of a class, an argument of a constructor. */
final case class Param(name: String, ty: Ty)
