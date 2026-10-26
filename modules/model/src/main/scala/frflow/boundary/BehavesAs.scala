package frflow
package boundary

/** `store.behavesAs(StoreModel)`: the boundary does what its model does. The formula of an assumption. */
final class BehavesAs[T, S] private[frflow] (val model: ModelOf) extends frflow.term.Term[Boolean](
  Tree.Lit(true, summon[LeanType[Boolean]]), summon[LeanType[Boolean]])

object BehavesAs:
  extension [T](boundary: Boundary[T])
    /** The boundary does what `model` does: `Node.assumption("…")(store.behavesAs(StoreModel))`. */
    def behavesAs[S](model: T & StateModel[S]): BehavesAs[T, S] = BehavesAs(ModelOf(boundary, model))
