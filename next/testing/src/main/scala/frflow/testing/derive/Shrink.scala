package frflow.testing.derive

import frflow.core.expr.Value
import frflow.core.ty.{DataType, Ty}
import frflow.core.vocab.Vocabulary

/** Smaller values of a type, the smallest first: what a failing case is shrunk with. `false` for `true`, numbers
  * towards 0, strings shorter, lists with fewer or smaller elements, an option empty, a component or field smaller,
  * and of an enum the cases without fields written before it.
  */
final class Shrink(v: Vocabulary):
  def of(x: Value, ty: Ty): LazyList[Value] = (x, ty) match
    case (Value.Bool(true), _)                   => LazyList(Value.Bool(false))
    case (Value.Num(n), _)                       =>
      LazyList(BigInt(0), n / 2, n - n.signum).distinct.filter(_ != n).map(Value.Num(_))
    case (Value.Str(s), _)                       =>
      LazyList("", s.take(s.length / 2), s.dropRight(1)).distinct.filter(_ != s).map(Value.Str(_))
    case (Value.Many(xs), Ty.ListOf(a))          => list(xs, of(_, a)).map(Value.Many(_))
    case (Value.Many(xs), Ty.SetOf(a))           => list(xs, of(_, a)).map(Value.Many(_))
    case (Value.Pairs(es), Ty.MapOf(k, w))       =>
      list(es, (a, b) => of(b, w).map(a -> _) #::: of(a, k).map(_ -> b)).map(Value.Pairs(_))
    case (Value.Maybe(Some(y)), Ty.OptionOf(a))  => Value.Maybe(None) #:: of(y, a).map(z => Value.Maybe(Some(z)))
    case (Value.Inject(s, y), Ty.EitherOf(l, r)) =>
      of(y, if s == frflow.core.expr.Side.Error then l else r).map(Value.Inject(s, _))
    case (Value.Tuple(xs), Ty.TupleOf(ts))       => each(xs, ts).map(Value.Tuple(_))
    case (Value.Data(c, fs), Ty.Data(n))         => v.dataType(n).fold(LazyList.empty)(d =>
        simpler(d, c) #::: each(fs, d.fieldsOf(c)).map(Value.Data(c, _)))
    case _                                       => LazyList.empty

  /** None, the first half, each element left out, then each element smaller. */
  private def list[A](xs: List[A], smaller: A => LazyList[A]): LazyList[List[A]] =
    if xs.isEmpty then LazyList.empty
    else (Nil #:: xs.take(xs.size / 2) #:: LazyList.from(xs.indices).map(i => xs.patch(i, Nil, 1))).distinct #:::
      LazyList.from(xs.indices).flatMap(i => smaller(xs(i)).take(4).map(y => xs.updated(i, y)))

  private def each(xs: List[Value], ts: List[Ty]): LazyList[List[Value]] =
    LazyList.from(xs.indices).flatMap(i => ts.lift(i).fold(LazyList.empty)(t => of(xs(i), t).map(xs.updated(i, _))))

  private def simpler(d: DataType, c: frflow.core.name.CtorName): LazyList[Value] = d match
    case DataType.Sum(_, _, cs) =>
      LazyList.from(cs.toList.takeWhile(_.name != c).filter(_.fields.isEmpty)).map(k => Value.Data(k.name, Nil))
    case DataType.Product(_, _, _) => LazyList.empty
