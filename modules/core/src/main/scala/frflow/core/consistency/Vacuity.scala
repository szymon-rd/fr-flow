package frflow.core.consistency

import frflow.core.name.NodeId
import frflow.core.ty.Ty

/** What guards a theory from saying nothing (owner §18), beside the positive statements of the model: each a small
  * proof that something can be, whose witness a search finds (`testing.Witnesses`: the generators given, then small
  * values of each type).
  */
enum Vacuity:
  /** `always[T](rule)` admits a value: some value of `T` meets the rule. */
  case Inhabited(statement: NodeId, ty: Ty)
  /** The `i`-th condition `A` of a claim's `A implies B` (`term.interpret.Conditions`) is satisfiable, over the
    * variables bound above it (`over`).
    */
  case Satisfiable(statement: NodeId, i: Int, over: List[Ty])
