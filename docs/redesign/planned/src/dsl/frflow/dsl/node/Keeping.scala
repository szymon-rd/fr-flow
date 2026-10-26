package frflow.dsl.node

import frflow.core.expr.Lambda
import frflow.core.spec.Written
import frflow.dsl.build.Deferred

/** How a contract or a design stands to an invariant: kept through a view of each call, or exempt with a reason. */
enum Keeping:
  case Kept(invariant: Parent, view: Deferred[Written[Lambda]])
  case Exempt(invariant: Parent, because: String)
