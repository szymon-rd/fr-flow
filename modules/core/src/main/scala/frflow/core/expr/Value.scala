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
  /** The models' states, and the faults the calls of a failing model's operations take in turn. */
  case World(states: List[(ModelName, Value)], faults: List[Boolean])

object Value:
  /** Every number a value holds, in order. */
  def numbers(v: Value): List[BigInt] = v match
    case Num(n)                  => List(n)
    case Data(_, fs)             => fs.flatMap(numbers)
    case Many(es)                => es.flatMap(numbers)
    case Maybe(e)                => e.toList.flatMap(numbers)
    case Pairs(es)               => es.flatMap((k, x) => numbers(k) ++ numbers(x))
    case Tuple(es)               => es.flatMap(numbers)
    case Inject(_, e)            => numbers(e)
    case World(ss, _)            => ss.flatMap((_, s) => numbers(s))
    case Bool(_) | Str(_) | Unit => Nil
