package frflow.dsl.node

/** The edges a node declares: the wholes it refines, the premises its proof assumes, the node it replaces. */
final case class Links(refines: List[Parent], assumes: List[Parent], replaces: Option[Parent])

object Links:
  val none: Links = Links(Nil, Nil, None)
