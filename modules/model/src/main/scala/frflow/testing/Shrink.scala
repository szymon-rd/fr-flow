package frflow
package testing

import frflow.types.Shape

/** Smaller values of a type, the smallest first: what a failing case is shrunk with. A value of a `fixed` type (one only
  * a given generator makes: what the outside can hold) is never shrunk, at any depth: a smaller one may be one the
  * outside cannot hold.
  */
private[frflow] object Shrink:
  def of(t: LeanType[?], v: Any, opaques: Map[String, LeanType[?]], fixed: LeanType[?] => Boolean = _ => false): LazyList[Any] =
    if fixed(t) then LazyList.empty else ofType(t, v, opaques, fixed)

  private def ofType(t: LeanType[?], v: Any, opaques: Map[String, LeanType[?]], fixed: LeanType[?] => Boolean): LazyList[Any] =
    def go(u: LeanType[?], x: Any) = of(u, x, opaques, fixed)
    def list(a: LeanType[?], xs: List[Any]): LazyList[List[Any]] =
      if xs.isEmpty then LazyList.empty
      else (Nil #:: xs.take(xs.size / 2) #:: LazyList.from(xs.indices).map(i => xs.patch(i, Nil, 1))) ++
        LazyList.from(xs.indices).flatMap(i => go(a, xs(i)).take(4).map(y => xs.updated(i, y)))
    (t.shape, v) match
      case (Shape.Prop, true)                => LazyList(false)
      case (Shape.Num(k), x)                 =>
        val n = x match { case i: Int => BigInt(i); case l: Long => BigInt(l); case b: BigInt => b; case _ => BigInt(0) }
        if n == 0 then LazyList.empty else LazyList(BigInt(0), n / 2, n - n.signum).distinct.filter(_ != n).map(k.of)
      case (Shape.Str, s: String)            =>
        if s.isEmpty then LazyList.empty else LazyList("", s.take(s.length / 2), s.dropRight(1)).distinct.filter(_ != s)
      case (Shape.ListOf(a), xs: List[?])    => list(a, xs)
      case (Shape.SetOf(a), xs: Set[?])      => list(a, xs.toList).map(_.toSet)
      case (Shape.MapOf(k, w), m: Map[?, ?]) => list(LeanType.of[Any](Shape.TupleOf(List(k, w))), m.toList).map(_.asInstanceOf[List[(Any, Any)]].toMap)
      case (Shape.OptionOf(a), Some(x))      => None #:: go(a, x).map(Some(_))
      case (Shape.EitherOf(e, _), Left(x))   => go(e, x).map(Left(_))
      case (Shape.EitherOf(_, a), Right(x))  => go(a, x).map(Right(_))
      case (Shape.TupleOf(as), p: Product)   =>
        val xs = p.productIterator.toList
        LazyList.from(xs.indices).flatMap(i => go(as(i), xs(i)).map(y => Tuple.fromArray(xs.updated(i, y).map(_.asInstanceOf[Object]).toArray)))
      case (Shape.FnOf(as, _), tb: Table)    =>
        if tb.entries.isEmpty then LazyList.empty
        else Table(as.size, Nil, tb.default) #:: LazyList.from(tb.entries.indices).map(i => Table(as.size, tb.entries.patch(i, Nil, 1), tb.default))
      case (Shape.Opq(o), x)                 => opaques.get(o.name).fold(LazyList.empty)(go(_, x))
      case (Shape.Data(adt), x)              =>
        val c = adt.ctorOf(x)
        // A case with no fields, earlier in the enum, is simpler; then each field smaller.
        val simpler = if adt.isEnum then adt.ctors.takeWhile(_ ne c).flatMap(_.singleton).to(LazyList) else LazyList.empty
        val fs = x.asInstanceOf[Product].productIterator.toList
        simpler ++ (if c.fields.isEmpty then LazyList.empty
          else LazyList.from(fs.indices).flatMap(i => go(c.fields(i)._2, fs(i)).map(y => c.make(fs.updated(i, y)))))
      case _ => LazyList.empty
