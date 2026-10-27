package frflow.proof.obligation

import frflow.core.name.SymbolName
import frflow.core.term.Stated

/** A witness as Lean is given it: a term built from a statement (`fun held request => …`, `term.interpret.Defining`)
  * of the open value it witnesses, or a value a search found.
  */
enum Supplied:
  case Term(t: Stated[?], of: SymbolName)
  case Value(c: Constant)
