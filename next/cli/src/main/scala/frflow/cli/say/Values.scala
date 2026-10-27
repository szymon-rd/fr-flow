package frflow.cli.say

import frflow.core.expr.{Side, Value}
import frflow.core.ty.{NumKind, Ty}

/** Values and types as the developer writes them in Scala: `Booking("Oak", 9, 10)`, `List[Booking]`. A case class's
  * constructor (`mk`) is left out of a value: its fields are shown in parentheses.
  */
object Values:
  def value(v: Value): String = v match
    case Value.Bool(b)            => b.toString
    case Value.Num(n)             => n.toString
    case Value.Str(s)             => "\"" + s + "\""
    case Value.Unit               => "()"
    case Value.Data(c, Nil)       => c.value
    case Value.Data(c, fs)        => s"${if c.value == "mk" then "" else c.value}(${all(fs)})"
    case Value.Many(es)           => s"List(${all(es)})"
    case Value.Maybe(e)           => e.fold("None")(x => s"Some(${value(x)})")
    case Value.Pairs(es)          => es.map((k, x) => s"${value(k)} -> ${value(x)}").mkString("Map(", ", ", ")")
    case Value.Tuple(es)          => s"(${all(es)})"
    case Value.Inject(Side.Error, e) => s"Left(${value(e)})"
    case Value.Inject(Side.Value, e) => s"Right(${value(e)})"
    case Value.World(states, _)   => states.map((m, s) => s"${m.value}: ${value(s)}").mkString("{", "; ", "}")

  def all(vs: List[Value]): String = vs.map(value).mkString(", ")

  def ty(t: Ty): String = t match
    case Ty.Bool                => "Boolean"
    case Ty.Str                 => "String"
    case Ty.Unit                => "Unit"
    case Ty.World               => "World"
    case Ty.Never               => "Nothing"
    case Ty.Num(k)              => num(k)
    case Ty.ListOf(a)           => s"List[${ty(a)}]"
    case Ty.OptionOf(a)         => s"Option[${ty(a)}]"
    case Ty.EitherOf(e, a)      => s"Either[${ty(e)}, ${ty(a)}]"
    case Ty.MapOf(k, v)         => s"Map[${ty(k)}, ${ty(v)}]"
    case Ty.SetOf(a)            => s"Set[${ty(a)}]"
    case Ty.TupleOf(as)         => as.map(ty).mkString("(", ", ", ")")
    case Ty.FnOf(ps, r)         => s"${ps.map(ty).mkString("(", ", ", ")")} => ${ty(r)}"
    case Ty.Sort(n)             => n.value
    case Ty.Data(n)             => n.value
    case Ty.FlowOf(r, e)        => s"F[${e.fold("")(x => s"${ty(x)} or ")}${ty(r)}]"

  private def num(k: NumKind): String = k match
    case NumKind.Int32 => "Int"
    case NumKind.Int64 => "Long"
    case NumKind.Big   => "BigInt"
