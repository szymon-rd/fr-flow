package frflow.proof.obligation

import frflow.core.name.{DefName, SymbolName}
import frflow.core.term.Stated

/** A witness as Lean is given it: a term built from a statement (`fun held request => …`, `term.interpret.Defining`)
  * of the open value it witnesses, or a value a search found. Proven code a later witness mentions stands as its
  * define, given the witnesses of what it leaves open (`Code`: `bookIfGranted_run` given `granted`'s); it is no
  * witness itself.
  */
enum Supplied:
  case Term(t: Stated[?], of: SymbolName)
  case Value(c: Constant)
  case Code(of: SymbolName, define: DefName)
