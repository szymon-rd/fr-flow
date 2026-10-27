package frflow.testing.derive

import frflow.core.expr.{Side, Value}
import frflow.core.ty.Ty
import frflow.core.vocab.Vocabulary

/** A value and every value it holds, each with its type: a list's and a set's elements, an option's value, an
  * `Either`'s side, a pair's components, a map's keys and values, a record's or an enum case's fields.
  */
final class Parts(v: Vocabulary):
  def apply(x: Value, ty: Ty): List[(Value, Ty)] = (x -> ty) :: ((x, ty) match
    case (Value.Many(xs), Ty.ListOf(a))          => xs.flatMap(apply(_, a))
    case (Value.Many(xs), Ty.SetOf(a))           => xs.flatMap(apply(_, a))
    case (Value.Maybe(o), Ty.OptionOf(a))        => o.toList.flatMap(apply(_, a))
    case (Value.Inject(s, y), Ty.EitherOf(l, r)) => apply(y, if s == Side.Error then l else r)
    case (Value.Tuple(xs), Ty.TupleOf(ts))       => xs.zip(ts).flatMap(apply(_, _))
    case (Value.Pairs(es), Ty.MapOf(k, w))       => es.flatMap((a, b) => apply(a, k) ++ apply(b, w))
    case (Value.Data(c, fs), Ty.Data(n))         =>
      fs.zip(v.dataType(n).toList.flatMap(_.fieldsOf(c))).flatMap(apply(_, _))
    case _                                       => Nil)
