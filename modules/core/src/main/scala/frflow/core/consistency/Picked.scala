package frflow.core.consistency

/** Which side of a defining relation the witness is, and by how much it is moved: `0` for an equation or a bound
  * that admits equality, `-1` below a strict upper bound, `+1` above a strict lower one.
  */
enum Picked:
  case Left(by: Int)
  case Right(by: Int)
