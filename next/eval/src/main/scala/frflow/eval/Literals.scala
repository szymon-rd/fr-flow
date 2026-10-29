package frflow.eval

import frflow.core.Elaborated
import frflow.core.expr.{Side, Value}
import frflow.core.name.ModelName
import frflow.core.term.World
import frflow.core.ty.{NumKind, Ty}

/** A constant as Scala holds it: data built through its type's `DataRep`, its fields typed by its declaration; a map
  * and a set as Scala's; a world as each model's state, by name, with its faults (`Faults`). The inverse of `Reflect`.
  */
final class Literals(e: Elaborated):
  def apply(v: Value, t: Ty): ScalaValue = ScalaValue(scala(v, t))

  /** A number at its kind, or a FrFlow bug where it does not fit: never wrapped around. */
  private def number(n: BigInt, k: NumKind): Any =
    if !k.holds(n) then throw IllegalStateException(s"FrFlow bug: the number $n read as a Scala $k, which cannot hold it")
    else k match
      case NumKind.Big   => n
      case NumKind.Int64 => n.toLong
      case NumKind.Int32 => n.toInt

  private def scala(v: Value, t: Ty): Any = (v, t) match
    case (Value.Bool(b), _)                => b
    case (Value.Str(s), _)                 => s
    case (Value.Num(n), Ty.Num(k))         => number(n, k)
    case (Value.Unit, _)                   => ()
    case (Value.Tuple(xs), Ty.TupleOf(ts)) => Tuple.fromArray(xs.zip(ts).map(scala(_, _)).toArray[Any])
    case (Value.Inject(s, x), Ty.EitherOf(l, r)) => if s == Side.Error then Left(scala(x, l)) else Right(scala(x, r))
    case (Value.Many(xs), Ty.ListOf(a))    => xs.map(scala(_, a))
    case (Value.Many(xs), Ty.SetOf(a))     => xs.map(scala(_, a)).toSet
    case (Value.Pairs(es), Ty.MapOf(k, w)) => es.map((a, b) => scala(a, k) -> scala(b, w)).toMap
    case (Value.Maybe(x), Ty.OptionOf(a))  => x.map(scala(_, a))
    case (Value.Data(c, fs), Ty.Data(n))   => e.reps(n).make(c, fs.zip(Fields.of(e, n, c)).map(scala(_, _)))
    case (Value.World(ss, faults), Ty.World) => world(ss, faults)
    case _ => throw IllegalStateException(s"FrFlow bug: the constant $v read at type $t")

  /** Each model's state at its model's type, and the faults when there are any. */
  private def world(states: List[(ModelName, Value)], faults: List[Boolean]): World =
    val held = states.map((m, s) => m -> scala(s, Races.typeOf(m).getOrElse(e.theory.vocabulary.model(m)
      .fold(Ty.Unit)(_.state)))).toMap
    World.of(if faults.isEmpty then held else held.updated(Faults.model, faults))
