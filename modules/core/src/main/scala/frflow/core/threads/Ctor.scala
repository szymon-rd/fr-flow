package frflow.core.threads

/** A constructor of an inductive type, over its arguments: `| name (x : T) (y : U)`. */
final case class Ctor(name: String, params: List[Param])
