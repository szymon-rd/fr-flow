package frflow.core.consistency

import frflow.core.name.SymbolName

/** What can be said of a group before Lean runs: a witness for everything open (Lean is then asked to check it), plain
  * Scala standing for some (evidence, listed so), or none for some ("consistency not proven", its own status: not a
  * failing proof).
  */
enum Standing:
  case Witnessed
  case Evidence(tested: List[SymbolName])
  case Unwitnessed(missing: List[SymbolName])

object Standing:
  def of(ws: List[Witness]): Standing =
    val missing = ws.collect { case Witness.Missing(s) => s }
    val tested = ws.collect { case Witness.Tested(s) => s }
    if missing.nonEmpty then Unwitnessed(missing) else if tested.nonEmpty then Evidence(tested) else Witnessed
