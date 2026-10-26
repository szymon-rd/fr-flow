package frflow.dsl.node

import frflow.core.code.Realization
import frflow.dsl.build.Deferred

/** The edges a node declares, and the implementations run against it (a model's `.checkedAgainst`, `.implementedBy`).
  */
final case class Links(under: List[Parent], replaces: Option[Parent], keeping: List[Keeping],
    realizations: List[Deferred[Realization]])

object Links:
  val none: Links = Links(Nil, None, Nil, Nil)
