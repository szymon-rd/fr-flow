package frflow.api.view.whole

import frflow.core.name.SymbolName

/** How a consistency obligation stands (owner §15, §18): Lean checked the witnesses; only tested Scala stands for
  * some open value (evidence, listed so); or neither ("consistency not proven", its own status).
  */
enum GroupStatus:
  case Proven
  case Evidence(tested: List[SymbolName])
  case NotProven
