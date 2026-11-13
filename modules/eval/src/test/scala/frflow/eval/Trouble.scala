package frflow.eval

import frflow.*

/** An enum of the tests' constants: a case with no fields, and one holding a number. */
enum Trouble derives RocqType:
  case Down
  case TooBig(n: BigInt)

object Trouble:
  /** A model naming the type, so its constants are read through its `DataRep`. */
  val anyTrouble: Node = Node.claim("A trouble is itself.")(forall((t: Term[Trouble]) => t === t))
  val knowledge: FrModel = FrModel("Troubles")(anyTrouble)
