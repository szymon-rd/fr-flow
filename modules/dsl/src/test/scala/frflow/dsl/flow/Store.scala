package frflow.dsl.flow

import frflow.dsl.model.StateModel
import frflow.dsl.term.Term
import frflow.dsl.vocab.{Declaration, Definition}
import frflow.dsl.vocab.Flow

/** Operations on a state of the tests, Definitions, and their model: a number kept, given back and replaced. */
object Store:
  val load = Declaration[Flow[BigInt]]("the number kept")
  val save = Declaration[BigInt => Flow[Unit]]("the number kept replaced")

  object kept extends StateModel[BigInt]("the number the tests keep"):
    load.means(state.get)
    save.means(n => state.set(n))

  /** The operations as a program calls them, as steps. */
  object recording:
    def load: Flow[BigInt] = Flow.step(Store.load)
    def save(n: Term[BigInt]): Flow[Unit] = Flow.step(Store.save(n))
