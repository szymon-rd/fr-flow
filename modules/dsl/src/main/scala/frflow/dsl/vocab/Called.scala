package frflow.dsl.vocab

import frflow.core.name.SymbolName
import frflow.core.term.language.Final
import frflow.dsl.term.{RocqType, Term}

/** A Definition applied to its arguments (`inRoom(request.room)`): the term `Definition.apply` makes, which also says
  * which Definition it applies and to what.
  */
final class Called[R](val definition: SymbolName, val args: List[Term[?]], run: Final[R])(using RocqType[R])
    extends Term[R](run)
