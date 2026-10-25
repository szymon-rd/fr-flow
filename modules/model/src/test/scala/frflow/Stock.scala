package frflow

/** A shelf's stock as a boundary: a flow over it is printed as a Lean `do` block, run on its model, and run on an
  * implementation, which is checked against the model.
  */
trait Stock:
  def count: Flow[BigInt]
  def add(n: Term[BigInt]): Flow[Unit]
