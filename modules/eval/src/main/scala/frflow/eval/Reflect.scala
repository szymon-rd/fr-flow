package frflow.eval

import frflow.core.Elaborated
import frflow.core.expr.{Side, Value}
import frflow.core.term.World
import frflow.core.ty.Ty

/** A Scala value as a `Value`, walked by its type through the `DataRep`s: what Scala computed, given to Lean to
  * evaluate against (`eval_i`, `probe_j`). The inverse of `Literals`; law: `Reflect(Literals(v, t), t) == v`.
  */
final class Reflect(e: Elaborated):
  def apply(v: ScalaValue, t: Ty): Value = (v.unwrap, t) match
    case (b: Boolean, _)                     => Value.Bool(b)
    case (s: String, _)                      => Value.Str(s)
    case (n: BigInt, _)                      => Value.Num(n)
    case (n: Long, _)                        => Value.Num(BigInt(n))
    case (n: Int, _)                         => Value.Num(BigInt(n))
    case ((), _)                             => Value.Unit
    case (o: Option[?], Ty.OptionOf(a))      => Value.Maybe(o.map(of(_, a)))
    case (xs: List[?], Ty.ListOf(a))         => Value.Many(xs.map(of(_, a)))
    case (xs: Set[?], Ty.SetOf(a))           => Value.Many(xs.toList.map(of(_, a)))
    case (m: Map[?, ?], Ty.MapOf(k, w))      => Value.Pairs(m.toList.map((a, b) => of(a, k) -> of(b, w)))
    case (x: Either[?, ?], Ty.EitherOf(l, r)) =>
      x.fold(a => Value.Inject(Side.Error, of(a, l)), b => Value.Inject(Side.Value, of(b, r)))
    case (p: Product, Ty.TupleOf(ts))        => Value.Tuple(p.productIterator.toList.zip(ts).map(of))
    case (_, Ty.World)                       => world(Fn.as[World](v))
    case (x, Ty.Data(n))                     =>
      val (c, fs) = e.reps(n).split(x)
      Value.Data(c, fs.zip(Fields.of(e, n, c)).map(of))
    case (x, _) => throw IllegalStateException(s"FrFlow bug: the value $x read at type $t")

  private def of(x: Any, t: Ty): Value = apply(ScalaValue(x), t)

  /** Each model's state at its model's type, in the vocabulary's order, the races' winners when it holds them, and
    * the faults.
    */
  private def world(w: World): Value =
    val states = e.theory.vocabulary.models.flatMap(m => w.state(m.name).map(s => m.name -> of(s, m.state))) ++
      w.state(Races.model).map(r => Races.model -> of(r, Ty.ListOf(Ty.Bool)))
    Value.World(states, w.state(Faults.model).fold(Nil)(fs => Fn.as[List[Boolean]](ScalaValue(fs))))
