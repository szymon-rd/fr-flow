package frflow.eval.run

import frflow.core.name.{DefName, NodeId}
import frflow.core.spec.Range
import frflow.core.Theory
import frflow.core.expr.Value
import frflow.core.ty.{DataType, Ty}
import frflow.eval.{Applied, Env, Fn, ScalaValue, Semantics}

/** An `always[T]`, enforced where a value is made: of each value of its type in a call (an input, the result; each
  * element of a list of them), in an example, a generated test and a generated value (`testing.Respecting`).
  */
final case class Made(always: NodeId, ty: Ty, rule: Applied, fields: (ScalaValue, Ty) => List[(ScalaValue, Ty)]):
  /** The `always` broken by one of `call`'s values (`types` theirs), if one is. */
  def broken(call: List[ScalaValue], types: List[Ty], env: Env): Option[Broken] =
    Option.unless(call.zip(types).flatMap(of).forall(holds(_, env)))(Broken.Always(always))

  def holds(v: ScalaValue, env: Env): Boolean = rule.run(env, List(v)).exists(Fn.bool)

  /** The values of `ty` in `v`: itself, a list's elements, a record's fields holding either. */
  private def of(v: ScalaValue, t: Ty): List[ScalaValue] = t match
    case `ty`            => List(v)
    case Ty.ListOf(`ty`) => Fn.list(v).map(ScalaValue(_))
    case Ty.Data(_)      => fields(v, t).flatMap(of)
    case _               => Nil

object Made:
  /** Every `always[T]` of the theory, its rule the define named as the node. */
  def of(semantics: Semantics, t: Theory): List[Made] = t.nodes.map(_.node).flatMap(n => n.statement.range.collect {
    case Range.Made(ty) =>
      t.vocabulary.define(DefName(n.id.value)).map(d => Made(n.id, ty, semantics.lambda(d.written),
        fieldsOf(semantics, t, ty)))
  }.flatten)

  /** A record's fields holding a `ty` or a list of them, read through the record's own `DataRep` (`Reflect`). */
  private def fieldsOf(semantics: Semantics, t: Theory, ty: Ty)(v: ScalaValue, of: Ty): List[(ScalaValue, Ty)] =
    of match
      case Ty.Data(n) => (semantics.reflect(v, of), t.vocabulary.dataType(n)) match
          case (Value.Data(_, fs), Some(DataType.Product(_, _, decl))) => fs.zip(decl).collect {
              case (f, d) if d.ty == ty || d.ty == Ty.ListOf(ty) => semantics.literal(f, d.ty) -> d.ty
            }
          case _                                                     => Nil
      case _          => Nil
