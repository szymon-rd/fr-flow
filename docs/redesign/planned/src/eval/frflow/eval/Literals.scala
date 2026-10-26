package frflow.eval

import frflow.core.Elaborated
import frflow.core.expr.{Side, Value}
import frflow.core.ty.{NumKind, Ty}

/** A constant as Scala holds it: data built through its type's `DataRep`, its fields typed by its declaration. The
  * inverse of `Reflect`.
  */
final class Literals(e: Elaborated):
  def apply(v: Value, t: Ty): ScalaValue = ScalaValue(scala(v, t))

  private def number(n: BigInt, k: NumKind): Any = k match
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
    case (Value.Maybe(x), Ty.OptionOf(a))  => x.map(scala(_, a))
    case (Value.Data(c, fs), Ty.Data(n))   => e.reps(n).make(c, fs.zip(Fields.of(e, n, c)).map(scala(_, _)))
    case _                                 => ??? // maps, sets, outcomes, worlds

