package frflow.dsl.vocab

import frflow.core.code.Code
import frflow.core.expr.Lambda
import frflow.core.name.DefName
import frflow.core.spec.Written
import frflow.dsl.build.Deferred

/** The meaning a Definition is given where it is written (owner §15: `define { … }` and `program { … }`): its proven
  * code, its written lambda (the vocabulary's define), and what a call names or production runs (`Spot`).
  */
final case class OnTheSpot(name: DefName, code: Code, lambda: Deferred[Written[Lambda]], spot: Spot)
