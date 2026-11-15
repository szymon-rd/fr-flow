package frflow.core.code

import frflow.core.expr.Value
import frflow.core.name.{DefName, SymbolName}
import frflow.core.threads.Datum

/** A file of code read from its TASTy: its name, and the tree it holds. */
final case class ReadUnit(name: String, tree: Datum)

/** What gives a Definition its meaning (owner §15): proven code (a define), plain Scala tested by properties, a
  * value fixed in the model, a value provided where the code runs (bound by examples, drawn by tests, passed in
  * production), or an execution of code read from its TASTy as trees (`Executing`: every statement about it is
  * stated of an execution of that code, and Rocq says what that is).
  */
enum Code:
  case Proven(define: DefName)
  case Tested(runs: ScalaCode, calls: List[SymbolName])
  case Valued(value: Value)
  case Provided
  case Executing(units: List[ReadUnit])

  /** The define Rocq proves, if any. */
  def proven: Option[DefName] = this match
    case Proven(d) => Some(d)
    case _         => None

  /** The Scala code it runs, if any. */
  def scala: Option[ScalaCode] = this match
    case Tested(r, _) => Some(r)
    case _            => None
