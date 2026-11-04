package frflow.api.node.tests

import frflow.core.expr.Value
import frflow.core.ty.Ty

/** What a report says beside its outcome: a generator the tests were given (its type, and what the developer said it
  * makes); the examples' values of a type its generator never makes; or that nothing varies between cases.
  */
enum Note:
  case Given(ty: Ty, says: Option[String])
  case NeverMade(ty: Ty, values: List[Value])
  case NothingToVary
