package frflow.testing.search

import frflow.core.expr.Value
import frflow.core.name.CtorName
import frflow.core.ty.{DataType, Ty}
import frflow.core.vocab.Vocabulary

/** The small values of each type, in order (a small-scope search, as SmallCheck enumerates them): two strings, four
  * numbers, lists of none, one and two small elements, each constructor over its fields' first few. A function, an
  * opaque type and a world have none here: a search over them finds nothing.
  */
final class Small(v: Vocabulary):
  val Width: Int = 3

  def of(t: Ty): List[Value] = t match
    case Ty.Bool        => List(Value.Bool(false), Value.Bool(true))
    case Ty.Num(_)      => List(0, 1, -1, 2).map(n => Value.Num(BigInt(n)))
    case Ty.Str         => List(Value.Str(""), Value.Str("a"))
    case Ty.Unit        => List(Value.Unit)
    case Ty.OptionOf(a) => Value.Maybe(None) :: of(a).take(Width).map(x => Value.Maybe(Some(x)))
    case Ty.ListOf(a)   =>
      val xs = of(a).take(Width)
      Value.Many(Nil) :: xs.map(x => Value.Many(List(x))) ++ xs.flatMap(x => xs.map(y => Value.Many(List(x, y))))
    case Ty.Data(n)     => v.dataType(n).toList.flatMap(data)
    case _              => Nil

  private def data(d: DataType): List[Value] = d match
    case DataType.Product(_, _, fs) => made(CtorName("mk"), fs.map(_.ty))
    case DataType.Sum(_, _, cs)     => cs.toList.flatMap(c => made(c.name, c.fields.map(_.ty)))

  /** A constructor over every combination of its fields' first small values. */
  private def made(c: CtorName, fields: List[Ty]): List[Value] =
    fields.foldRight(List(List.empty[Value]))((f, rest) => of(f).take(Width).flatMap(x => rest.map(x :: _)))
      .map(Value.Data(c, _))
