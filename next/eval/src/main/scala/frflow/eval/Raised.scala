package frflow.eval

import frflow.core.ty.Ty
import scala.util.control.NoStackTrace

/** An error a program raised, or a failing model's operation's call failed with: its value and its type, and, for
  * a failure of the operation's Scala, what it failed with. A handler of errors of that type is given it; any other passes it
  * on. What `Running` and `flow.FlowInterpreter` raise in `F`.
  */
final class Raised(val error: ScalaValue, val ty: Ty, val cause: Option[Throwable])
    extends RuntimeException(s"a program failed with an error of type $ty"), NoStackTrace:
  cause.foreach(c => { val _ = initCause(c) })

object Raised:
  /** A program's own error, raised. */
  def apply(error: ScalaValue, ty: Ty): Raised = new Raised(error, ty, None)
