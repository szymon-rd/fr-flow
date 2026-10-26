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
  /** The models' states, and the faults a failing boundary's calls take in turn. */
  case World(states: List[(ModelName, Value)], faults: List[Boolean])
