package frflow.core.expr

import frflow.core.name.{CtorName, ModelName}

/** A constant of the term language: data reified from a Scala value. Maps and sets keep their iteration order. */
enum Value:
  case Bool(b: Boolean)
  case Num(n: BigInt)
  case Str(s: String)
  case Unit
  case Data(ctor: CtorName, fields: List[Value])
  case Many(elems: List[Value])
  case Maybe(elem: Option[Value])
  case Pairs(entries: List[(Value, Value)])
  case Tuple(elems: List[Value])
  /** One side of an outcome or an `Either`: the error (`Left`) or the value (`Right`). */
  case Inject(side: Side, elem: Value)
  /** The models' states, and the faults a failing boundary's calls take in turn. */
  case World(states: List[(ModelName, Value)], faults: List[Boolean])
