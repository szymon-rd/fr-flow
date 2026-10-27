package frflow.eval.run

import frflow.core.analysis.Guards
import frflow.core.name.{DefName, NodeId}
import frflow.core.spec.Range
import frflow.core.Theory
import frflow.core.expr.Value
import frflow.core.ty.Ty
import frflow.eval.{Applied, Env, Fn, ScalaValue, Semantics}

/** An `always[T]`, enforced where a value is made: of each `T` a value in a call holds (an input, the result), as
  * its guard reaches it in Lean (`Guards`: a list's elements, an option's value, an `Either`'s side, a pair's
  * components, a record's or an enum case's fields), in an example, a generated test and a generated value
  * (`testing.Respecting`).
  */
final case class Made(always: NodeId, ty: Ty, rule: Applied, fields: (ScalaValue, Ty) => List[(ScalaValue, Ty)]):
  /** The `always` broken by one of `call`'s values (`types` theirs), if one is. */
  def broken(call: List[ScalaValue], types: List[Ty], env: Env): Option[Broken] =
    Option.unless(call.zip(types).flatMap(of).forall(holds(_, env)))(Broken.Always(always))

  def holds(v: ScalaValue, env: Env): Boolean = rule.run(env, List(v)).exists(Fn.bool)

  /** The values of `ty` in `v` (of type `t`). */
  private def of(v: ScalaValue, t: Ty): List[ScalaValue] = t match
    case `ty`              => List(v)
    case Ty.ListOf(a)      => Fn.list(v).flatMap(x => of(ScalaValue(x), a))
    case Ty.OptionOf(a)    => Fn.as[Option[Any]](v).toList.flatMap(x => of(ScalaValue(x), a))
    case Ty.EitherOf(e, a) => Fn.as[Either[Any, Any]](v).fold(x => of(ScalaValue(x), e), x => of(ScalaValue(x), a))
    case Ty.TupleOf(as)    => Fn.as[Product](v).productIterator.toList.zip(as).flatMap((x, a) => of(ScalaValue(x), a))
    case Ty.Data(_)        => fields(v, t).flatMap(of)
    case _                 => Nil

object Made:
  /** Every `always[T]` of the theory, its rule the define named as the node. */
  def of(semantics: Semantics, t: Theory): List[Made] = t.nodes.map(_.node).flatMap(n => n.statement.range.collect {
    case Range.Made(ty) =>
      t.vocabulary.define(DefName(n.id.value)).map(d => Made(n.id, ty, semantics.lambda(d.written),
        fieldsOf(semantics, t, ty)))
  }.flatten)

  /** A record's fields (an enum's, of its case) holding a `ty`, read through the record's own `DataRep`
    * (`Reflect`).
    */
  private def fieldsOf(semantics: Semantics, t: Theory, ty: Ty)(v: ScalaValue, of: Ty): List[(ScalaValue, Ty)] =
    of match
      case Ty.Data(n) => (semantics.reflect(v, of), t.vocabulary.dataType(n)) match
          case (Value.Data(c, fs), Some(d)) => fs.zip(d.fieldsOf(c)).collect {
              case (f, fty) if Guards.applies(t, ty, fty) => semantics.literal(f, fty) -> fty
            }
          case _                            => Nil
      case _          => Nil
