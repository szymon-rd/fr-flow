package frflow.core.ty

/** Which Scala integer a number is. Lean has one unbounded `Int`; Scala's `Int` and `Long` wrap around, so the IR keeps
  * them apart: they compare, but do not add, and nothing may be said to exist of a type that holds one.
  */
enum NumKind:
  case Int32, Int64, Big
  def bounded: Boolean = this != Big

  /** Whether a number of this kind can be `n`. */
  def holds(n: BigInt): Boolean = this match
    case Int32 => n.isValidInt
    case Int64 => n.isValidLong
    case Big   => true

  /** `n` if this kind can hold it, else the nearest number it can. */
  def nearest(n: BigInt): BigInt = this match
    case Int32 => n.max(BigInt(Int.MinValue)).min(BigInt(Int.MaxValue))
    case Int64 => n.max(BigInt(Long.MinValue)).min(BigInt(Long.MaxValue))
    case Big   => n
