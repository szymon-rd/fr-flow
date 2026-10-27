package frflow.dsl.node

import frflow.core.code.Realization
import frflow.dsl.build.Deferred

/** The edges a node declares (the wholes it refines, the premises its proof assumes, the node it replaces), and the
  * implementations run against it.
  */
final case class Links(refines: List[Parent], assumes: List[Parent], replaces: Option[Parent],
    realizations: List[Deferred[Realization]])

object Links:
  val none: Links = Links(Nil, Nil, None, Nil)
