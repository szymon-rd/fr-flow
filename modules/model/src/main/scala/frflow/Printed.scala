package frflow

/** One expression's Lean: the text, and what it mentions (in the order it meets them). */
private[frflow] final case class Printed(params: List[(String, String)], result: String, body: String, types: List[TypeDecl],
    opaques: List[Opaque], paramRefs: List[(String, String)], paramObjects: List[Param[?]], defs: List[Def[?]],
    boundaries: List[Boundary[?]] = Nil, world: Boolean = false, errors: List[String] = Nil, commutes: List[Commute] = Nil)
