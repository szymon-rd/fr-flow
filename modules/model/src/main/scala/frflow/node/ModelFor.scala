package frflow
package node

/** `Node.assumption(db)(DatabaseModel)(id, statement, why, idea)`. */
final class ModelFor[T](boundary: Boundary[T]):
  def apply[S](model: T & StateModel[S]): ModelNode[T, S] = ModelNode(ModelOf(boundary, model))
