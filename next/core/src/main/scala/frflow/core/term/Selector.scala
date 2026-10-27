package frflow.core.term

import frflow.core.name.TypeName
import frflow.core.ty.Ty

/** A field of a record type: its name and position, the record's type name, its type, and Scala's own getter and copy
  * of it (derived per type: no interpreter casts).
  */
final case class Selector[R, F](name: String, index: Int, record: TypeName, ty: Ty, get: R => F, set: (R, F) => R)

object Selector:
  /** A tuple, as Lean nests it (`Prod`): its components are fields `1` and `2`, the `i`-th of more `p.2.1`. */
  val pair: TypeName = TypeName("Prod")

  def first[A, B](ty: Ty): Selector[(A, B), A] = Selector("1", 0, pair, ty, _._1, (p, a) => (a, p._2))
  def second[A, B](ty: Ty): Selector[(A, B), B] = Selector("2", 1, pair, ty, _._2, (p, b) => (p._1, b))
