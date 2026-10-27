package frflow.testing.report

import frflow.core.expr.Value
import frflow.core.ty.Ty

/** What a report says beside its outcome: a generator the tests were given, and what the developer said it makes; the
  * examples' values of its type it never makes (they are drawn anyway, as seeds); or that nothing varies between
  * cases (the claim reads no input and the code is given nothing).
  */
enum Note:
  case Given(made: Made)
  case NeverMade(ty: Ty, values: List[Value])
  case NothingToVary
