package frflow.eval

import frflow.core.Elaborated
import frflow.core.expr.Value
import frflow.core.ty.Ty

/** A constant as Scala holds it: data built through its type's `DataRep`, its fields typed by its declaration. The
  * inverse of `Reflect`.
  */
final class Literals(e: Elaborated):
  def apply(v: Value, t: Ty): ScalaValue = ScalaValue(scala(v, t))

  private def scala(v: Value, t: Ty): Any = (v, t) match
    case (Value.Bool(b), _)                => b
    case (Value.Str(s), _)                 => s
    case (Value.Many(xs), Ty.ListOf(a))    => xs.map(scala(_, a))
    case (Value.Maybe(x), Ty.OptionOf(a))  => x.map(scala(_, a))
    case (Value.Data(c, fs), Ty.Data(n))   => e.reps(n).make(c, fs.zip(Fields.of(e, n, c)).map(scala(_, _)))
    case _                                 => ??? // numbers by kind, maps, sets, tuples, outcomes, worlds

