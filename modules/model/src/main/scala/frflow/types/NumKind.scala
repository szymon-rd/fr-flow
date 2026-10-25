package frflow
package types

/** Which Scala number a Lean `Int` is: what a generated value must be. */
private[frflow] enum NumKind:
  case IntN, LongN, BigN
  def bounded: Boolean = this != BigN
  def of(n: BigInt): Any = this match
    case IntN  => n.toInt
    case LongN => n.toLong
    case BigN  => n
