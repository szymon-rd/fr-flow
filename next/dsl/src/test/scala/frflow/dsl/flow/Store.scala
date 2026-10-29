package frflow.dsl.flow

import frflow.core.term.Program
import frflow.dsl.model.StateModel
import frflow.dsl.term.Term
import frflow.dsl.vocab.Definition

/** Operations on a state of the tests, Definitions, and their model: a number kept, given back and replaced. */
object Store:
  val load = Definition[Program[BigInt]]("the number kept")
  val save = Definition[BigInt => Program[Unit]]("the number kept replaced")

  object kept extends StateModel[BigInt]("the number the tests keep"):
    load.means(state.get)
    save.means(n => state.set(n))

  /** The operations as a program calls them, recorded. */
  object recording:
    def load: Recorded[Term[BigInt]] = Flow[Recorded].step(Store.load)
    def save(n: Term[BigInt]): Recorded[Unit] = Flow[Recorded].run(Store.save(n))
