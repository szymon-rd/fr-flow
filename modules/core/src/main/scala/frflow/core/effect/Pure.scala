package frflow.core.effect

/** The type of a value of the code read, as a tree has it: a number of 32 bits, a truth value, nothing, an
  * object by where it is (of any class: the heap says which), or several values together (a loop's state).
  */
enum EType:
  case Int, Bool, Unit, Ref
  case Several(of: List[EType])

/** An operation with no effect: on numbers (wrapped as the JVM wraps them), on truth values, on objects. */
enum Prim:
  case Add, Sub, Mul, Neg, Less, LessEq, More, MoreEq, SameInt, And, Or, Not, SameBool, SameRef

/** What code computes with no effect: a term of the prover, no node of a tree. */
enum Pure:
  case Local(name: String)
  case Whole(value: BigInt)
  case Truth(value: Boolean)
  case Nothing
  case NoObject
  case Applied(op: Prim, to: List[Pure])
  case Choice(test: Pure, yes: Pure, no: Pure)
  case Several(of: List[Pure])

  /** Whether writing it again where it is used costs nothing: a name or a constant. */
  def atomic: Boolean = this match
    case Local(_) | Whole(_) | Truth(_) | Nothing | NoObject => true
    case _                                                   => false
