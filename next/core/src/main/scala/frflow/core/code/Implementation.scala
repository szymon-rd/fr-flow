package frflow.core.code

import frflow.core.name.{SourceText, SymbolName}

/** The plain Scala of a model's operations (`implementTested(ops*)(start, observe)(calls)`), whoever wrote it (owner
  * §36): the operations, in the order `calls` gives their functions; the Scala itself (`Implementation.Scala`); the
  * effect each function's result is in, by its `MonadThrow` instance (what tests it against the model and what binds
  * it where the code runs refuse another effect); and the code as written, with the files it refers to (governed).
  * A handle on Scala: never compared or printed.
  */
final class Implementation(val ops: List[SymbolName], val scala: Implementation.Scala, val effect: AnyRef,
    val written: SourceText, val files: List[CodeFile])

object Implementation:
  /** How the Scala is made holding a state of the model (`start`), how its state is read back (`observe`), and each
    * operation's function of the value `start` makes, in order (`calls`): each a function of plain values whose
    * result is in the implementation's effect.
    */
  final class Scala(val start: Any => Any, val observe: Any => Any, val calls: Any => List[Any])
