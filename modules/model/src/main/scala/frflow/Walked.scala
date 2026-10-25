package frflow

/** A Lean type's text and the declarations it needs, in the order Lean must read them. */
private[frflow] final case class Walked(lean: String, types: List[TypeDecl], opaques: List[Opaque])
