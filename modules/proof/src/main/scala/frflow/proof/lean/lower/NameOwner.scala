package frflow.proof.lean.lower

import frflow.core.name.VarId

/** What took a name in an expression: a variable of the IR, or a helper variable the lowering introduces itself (the
  * `k` of a map's `fun k => if k = …`), numbered in the order made.
  */
enum NameOwner:
  case Variable(id: VarId)
  case Helper(n: Int)
