package frflow.dsl.lifted.steps

/** What a port is to the reader of Scala that changes it: the type `S` of its state, the type of the port's one
  * `var`. Found by the compiler for any port class (`derived`), so `updating`'s type says the state it passes.
  */
trait PortState[P]:
  type S

object PortState:
  transparent inline given derived[P]: PortState[P] = ${ StepReader.state[P] }
