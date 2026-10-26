package frflow.dsl.vocab

import frflow.core.code.Code
import frflow.core.expr.Lambda
import frflow.core.name.DefName
import frflow.core.spec.Written
import frflow.core.term.Body
import frflow.dsl.build.Deferred

/** The meaning a Definition is given where it is written (owner §15: `define { … }` and `program { … }`): its proven
  * code, its written lambda (the vocabulary's define), and, for a define, its body, which a call names.
  */
final case class OnTheSpot(name: DefName, code: Code, lambda: Deferred[Written[Lambda]], body: Option[Body[?]])
