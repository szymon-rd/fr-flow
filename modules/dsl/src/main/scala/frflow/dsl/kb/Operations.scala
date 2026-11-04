package frflow.dsl.kb

import frflow.core.code.Implementation
import frflow.core.name.{RelPath, SymbolName}

/** The plain Scala the FrModel gives operations on one state (`implementTested(inRoom, add)(start, observe)(calls)`):
  * the operations' Definitions, in the order `calls` gives their functions, the implementation, and the model file
  * it is given in.
  */
final case class Operations(definitions: List[SymbolName], implementation: Implementation, writtenIn: RelPath)
