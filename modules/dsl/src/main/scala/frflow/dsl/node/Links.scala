package frflow.dsl.node

/** The edges a node declares: the wholes it refines, the premises its proof assumes, the node it replaces; and the
  * parts it says it is from (`.from`), read when the model is elaborated, so that a part may be declared after it.
  */
final case class Links(refines: List[Parent], assumes: List[Parent], replaces: Option[Parent],
    parts: List[() => Seq[Node | Null]] = Nil)

object Links:
  val none: Links = Links(Nil, Nil, None)
