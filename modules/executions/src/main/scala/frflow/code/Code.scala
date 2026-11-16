package frflow.code

import frflow.{Call as _, *}
import frflow.executions.Call
import frflow.values.{Obj, Value}
import scala.annotation.unused

// Real code in a statement. A method, function or constructor applied to the statement's terms is written as the
// code is (`s.add(x)`, `supervised(body)`), typed against the real classes, and read as the call it is: named as
// the tree read from the code's TASTy names the method. It is never run.

/** Raised if code written in a statement is run: it is only read. */
final class NotRun extends IllegalStateException("code written in a statement is read as a call, never run")

/** Where code is written in a statement, a term stands for the value the code takes. */
object InCode:
  given objectInCode[C](using @unused st: Stating): Conversion[Obj[C], C] = _ => throw NotRun()
  given truthInCode(using @unused st: Stating): Conversion[Term[Boolean], Boolean] = _ => throw NotRun()
  given numberInCode(using @unused st: Stating): Conversion[Term[BigInt], Int] = _ => throw NotRun()
  given textInCode(using @unused st: Stating): Conversion[Term[String], String] = _ => throw NotRun()

extension [A](code: Obj[() => A])
  /** The code where code takes it unevaluated (a by-name argument): `h.startThread(code.byName)`. */
  def byName(using @unused st: Stating): A = throw NotRun()

/** The call the code written is: `call(s.add(x))`. Where a word of a call follows the code (`s.add(x).atomic`), the
  * code is read so without it.
  */
inline def call[A](inline code: A): Call[A] = ${ CodeMacros.call[A]('code) }

implicit inline def codeAsCall[A](inline code: A): Call[A] = ${ CodeMacros.call[A]('code) }

/** Every name a method of the class can be called by: each method the class has, as the class it has it from
  * names it, and as each class that declares it above names it.
  */
inline def methodsOf[C]: List[String] = ${ CodeMacros.methods[C] }

/** The method the code calls, as the tree read names it: `methodOf[KeySet](_.add(???))`. */
inline def methodOf[C](inline code: C => Any): String = ${ CodeMacros.method[C]('code) }

/** A call by which the code applies a function itself: a local method called by its name, a function it holds
  * applied. An execution names every such call by one method, whatever interface the function is of; what
  * applies a function from outside the code names the interface's method (`r.run()`).
  */
def applicationOf[A](function: Term[Value], arguments: Term[Value]*): Call[A] =
  Call.of[A](Applied, (function +: arguments)*)

/** The method an execution names the code's own applications of a function by. */
val Applied: String = "scala.Function apply"
