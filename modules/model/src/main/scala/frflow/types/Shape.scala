package frflow
package types

private[frflow] enum Shape:
  case Prop, Str, UnitT, Unknown
  /** A Scala Int, Long or BigInt: the first two wrap around where Lean's Int does not. */
  case Num(kind: NumKind)
  case ListOf(a: LeanType[?])
  case OptionOf(a: LeanType[?])
  /** A flow's outcome (`attempt`): an error or a value. Lean's `Except E A`. */
  case EitherOf(e: LeanType[?], a: LeanType[?])
  case MapOf(k: LeanType[?], v: LeanType[?])
  case SetOf(a: LeanType[?])
  case TupleOf(as: List[LeanType[?]])
  case FnOf(as: List[LeanType[?]], r: LeanType[?])
  case Opq(o: Opaque)
  case Data(adt: Adt)
  /** The states of the boundaries' models (Lean's `World`). */
  case WorldT
  /** A flow's result, as an operation's: run from a world, the result and the world after. */
  case FlowOf(r: LeanType[?])
