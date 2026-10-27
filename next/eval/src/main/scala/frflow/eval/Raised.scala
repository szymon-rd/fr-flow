package frflow.eval

import frflow.core.ty.Ty

/** An error a program raised, or a failing boundary's call failed with: its value and its type. A handler of errors
  * of that type is given it; any other passes it on. What `Running` and `flow.FlowInterpreter` raise in `F`.
  */
final class Raised(val error: ScalaValue, val ty: Ty)
    extends Exception(s"a program failed with an error of type $ty", null, false, false)
