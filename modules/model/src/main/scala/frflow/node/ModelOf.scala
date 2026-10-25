package frflow
package node

/** A boundary and the model it is decided to behave as, with the implementations of the boundary checked against it. */
final case class ModelOf(boundary: Boundary[?], model: StateModel[?], impls: List[ModelImpl] = Nil)
