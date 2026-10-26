package frflow.dsl.term

import cats.syntax.all.*
import frflow.core.expr.{Side, Value}
import frflow.core.ty.Ty
import frflow.dsl.build.{Declarations, Declared, Fault}

/** A Scala value as a `Value`, walked by its type through the `DataRep`s its `LeanType` declares. */
object Reify:
  def apply[A](t: LeanType[A], a: A): Either[Fault, Value] = Walk(t.declares).value(t.ty, a)

  private final class Walk(declared: Declarations):
    def value(ty: Ty, a: Any): Either[Fault, Value] = (ty, a) match
      case (Ty.Bool, b: Boolean)          => Right(Value.Bool(b))
      case (Ty.Str, s: String)            => Right(Value.Str(s))
      case (Ty.Num(_), n: BigInt)         => Right(Value.Num(n))
      case (Ty.Num(_), n: Int)            => Right(Value.Num(BigInt(n)))
      case (Ty.Unit, ())                  => Right(Value.Unit)
      case (Ty.ListOf(e), xs: List[?])    => xs.traverse(value(e, _)).map(Value.Many(_))
      case (Ty.OptionOf(e), o: Option[?]) => o.traverse(value(e, _)).map(Value.Maybe(_))
      case (Ty.TupleOf(ts), p: Product)   => ts.zip(p.productIterator.toList).traverse(value).map(Value.Tuple(_))
      case (Ty.EitherOf(l, _), Left(x))   => value(l, x).map(Value.Inject(Side.Error, _))
      case (Ty.EitherOf(_, r), Right(x))  => value(r, x).map(Value.Inject(Side.Value, _))
      case (Ty.Data(n), x)                =>
        declared.types.get(n).flatMap(_.headOption).fold(Left(Fault.NoType(n.value)))(data(_, x))
      case _                              => ??? // maps, sets, worlds, as today's

    /** A value of a domain type taken apart by its `DataRep`, its fields walked by their declared types. */
    private def data(d: Declared, a: Any): Either[Fault, Value] =
      val (c, fields) = d.rep.split(a)
      d.data.fieldsOf(c).zip(fields).traverse(value).map(Value.Data(c, _))
