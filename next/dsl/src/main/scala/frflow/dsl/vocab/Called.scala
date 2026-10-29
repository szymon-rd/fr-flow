package frflow.dsl.vocab

import frflow.core.name.SymbolName
import frflow.core.term.Final
import frflow.dsl.term.{LeanType, Term}

/** A Definition applied to its arguments (`inRoom(request.room)`): the term `Definition.apply` makes, which also says
  * which Definition it applies and to what, so a program's step reads an operation's call off it (`Flow.step`).
  */
final class Called[R](val definition: SymbolName, val args: List[Term[?]], run: Final[R])(using LeanType[R])
    extends Term[R](run)

object Called:
  /** The Definition a step calls and its arguments: an application, or a Definition of no input itself (`now`). */
  def of(t: Term[?]): Option[(SymbolName, List[Term[?]])] = t match
    case c: Called[?]     => Some(c.definition -> c.args)
    case d: Definition[?] => Some(d.name -> Nil)
    case _                => None
