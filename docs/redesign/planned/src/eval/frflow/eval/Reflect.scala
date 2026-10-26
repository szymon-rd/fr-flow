package frflow.eval

import frflow.core.Elaborated
import frflow.core.expr.Value
import frflow.core.ty.Ty

/** A Scala value as a `Value`, walked by its type through the `DataRep`s: what Scala computed, given to Lean to
  * evaluate against (`eval_i`, `probe_j`). The inverse of `Literals`; law: `Reflect(Literals(v, t), t) == v`.
  */
final class Reflect(e: Elaborated):
  def apply(v: ScalaValue, t: Ty): Value = (v.unwrap, t) match
    case (b: Boolean, _)                    => Value.Bool(b)
    case (s: String, _)                     => Value.Str(s)
    case (n: BigInt, _)                     => Value.Num(n)
    case (n: Long, _)                       => Value.Num(BigInt(n))
    case (n: Int, _)                        => Value.Num(BigInt(n))
    case (o: Option[?], Ty.OptionOf(a))     => Value.Maybe(o.map(x => apply(ScalaValue(x), a)))
    case (xs: List[?], Ty.ListOf(a))        => Value.Many(xs.map(x => apply(ScalaValue(x), a)))
    case (x, Ty.Data(n))                    =>
      val (c, fs) = e.reps(n).split(x)
      Value.Data(c, fs.zip(Fields.of(e, n, c)).map((f, ft) => apply(ScalaValue(f), ft)))
    case _                                  => ??? // maps, sets, tuples, outcomes, worlds
