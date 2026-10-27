package frflow.web.json

import frflow.api.view.Tally
import frflow.core.expr.{Side, Value}
import frflow.core.name.*
import frflow.core.ty.{NumKind, Ty}
import frflow.decision.ledger.Decision
import io.circe.syntax.*
import io.circe.{Encoder, Json}

/** How the page reads what the views are made of: names as their text, values and types as the developer writes
  * them in Scala, a tally as its counts, and a decision as who took it, when and why (not the content it binds).
  */
object Leaves:
  given Encoder[NodeId] = Encoder.encodeString.contramap(_.value)
  given Encoder[RelPath] = Encoder.encodeString.contramap(_.value)
  given Encoder[SymbolName] = Encoder.encodeString.contramap(_.value)
  given Encoder[DefName] = Encoder.encodeString.contramap(_.value)
  given Encoder[TypeName] = Encoder.encodeString.contramap(_.value)
  given Encoder[ModelName] = Encoder.encodeString.contramap(_.value)
  given Encoder[BoundaryName] = Encoder.encodeString.contramap(_.value)
  given Encoder[OpName] = Encoder.encodeString.contramap(_.value)
  given Encoder[Value] = Encoder.encodeString.contramap(value)
  given Encoder[Ty] = Encoder.encodeString.contramap(ty)

  /** `[{"of": kind, "count": n}]`, each kind counted at least once. */
  given [K: Encoder]: Encoder[Tally[K]] = Encoder.instance(t =>
    Json.arr(t.counts.toList.map((k, n) => Json.obj("of" -> k.asJson, "count" -> n.asJson))*))

  given Encoder[Decision] = Encoder.instance(d => Json.obj("action" -> d.action.toString.toLowerCase.asJson,
    "by" -> d.author.by.asJson, "at" -> d.author.at.asJson, "reason" -> d.reason.text.asJson,
    "rejected" -> d.reason.rejected.asJson))

  def value(v: Value): String = v match
    case Value.Bool(b)               => b.toString
    case Value.Num(n)                => n.toString
    case Value.Str(s)                => "\"" + s + "\""
    case Value.Unit                  => "()"
    case Value.Data(c, Nil)          => c.value
    case Value.Data(c, fs)           => s"${if c.value == "mk" then "" else c.value}(${fs.map(value).mkString(", ")})"
    case Value.Many(es)              => es.map(value).mkString("List(", ", ", ")")
    case Value.Maybe(e)              => e.fold("None")(x => s"Some(${value(x)})")
    case Value.Pairs(es)             => es.map((k, x) => s"${value(k)} -> ${value(x)}").mkString("Map(", ", ", ")")
    case Value.Tuple(es)             => es.map(value).mkString("(", ", ", ")")
    case Value.Inject(Side.Error, e) => s"Left(${value(e)})"
    case Value.Inject(Side.Value, e) => s"Right(${value(e)})"
    case Value.World(states, _)      => states.map((m, s) => s"${m.value}: ${value(s)}").mkString("{", "; ", "}")

  def ty(t: Ty): String = t match
    case Ty.Num(k)         => k match { case NumKind.Int32 => "Int"; case NumKind.Int64 => "Long"; case _ => "BigInt" }
    case Ty.ListOf(a)      => s"List[${ty(a)}]"
    case Ty.OptionOf(a)    => s"Option[${ty(a)}]"
    case Ty.EitherOf(e, a) => s"Either[${ty(e)}, ${ty(a)}]"
    case Ty.MapOf(k, v)    => s"Map[${ty(k)}, ${ty(v)}]"
    case Ty.SetOf(a)       => s"Set[${ty(a)}]"
    case Ty.TupleOf(as)    => as.map(ty).mkString("(", ", ", ")")
    case Ty.FnOf(ps, r)    => s"${ps.map(ty).mkString("(", ", ", ")")} => ${ty(r)}"
    case Ty.Sort(n)        => n.value
    case Ty.Data(n)        => n.value
    case Ty.FlowOf(r, e)   => s"F[${e.fold("")(x => s"${ty(x)} or ")}${ty(r)}]"
    case Ty.Bool           => "Boolean"
    case Ty.Str            => "String"
    case Ty.Unit           => "Unit"
    case Ty.World          => "World"
    case Ty.Never          => "Nothing"

