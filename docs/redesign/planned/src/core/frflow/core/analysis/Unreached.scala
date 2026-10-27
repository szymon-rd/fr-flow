package frflow.core.analysis

import frflow.core.expr.{Expr, Exprs, Quantifier}
import frflow.core.spec.Range
import frflow.core.Theory
import frflow.core.ty.{DataType, Ty}
import frflow.core.vocab.SymbolType

/** The places a guard of `always[T]` would go but cannot yet (owner §16: an `always` holds wherever FrFlow covers
  * the code): a type holding a `T` (`Scope.holds`) inside a map, a set or a function value, which `Guards` does not
  * walk. A place is a type a statement quantifies over, a store's state, an input or the result of a Definition or a
  * store operation, and a field of a domain type. A Definition's own function type is not one (its inputs and result
  * are), nor is a program's result (its `made_` is step 3's).
  */
object Unreached:
  def of(t: Theory): List[Problem] =
    val all = places(t).filter { case (Ty.FlowOf(_), _) => false; case _ => true }
    t.nodes.map(_.node).flatMap(n => n.statement.range.toList.flatMap {
      case Range.Made(ty) => all.collect {
          case (x, at) if Scope.holds(t, ty, x) && !Guards.applies(t, ty, x) => Problem.AlwaysNotReached(n.id, x, at)
        }
      case _              => Nil
    }).distinct

  private def places(t: Theory): List[(Ty, String)] =
    val v = t.vocabulary
    val quantified = t.nodes.map(_.node).flatMap(n => n.statement.said.toList.flatMap(f => Exprs.all(f.value).collect {
      case Expr.Quant(Quantifier.Forall | Quantifier.Exists, xs, _) => xs.map(_.ty -> s"a variable of ${n.id.value}")
    }.flatten))
    val definitions = v.symbols.flatMap(s => s.ty match
      case SymbolType.Typed(Ty.FnOf(ins, r)) => ins.map(_ -> s"an input of ${s.name.value}") :+
          (r -> s"the result of ${s.name.value}")
      case SymbolType.Typed(x)               => List(x -> s.name.value)
      case _                                 => Nil)
    val ops = v.boundaries.flatMap(b => b.ops.flatMap(o => o.params.map(_._2 -> s"an input of ${o.name.value}") :+
      (o.result -> s"the result of ${o.name.value}")))
    val fields = v.types.flatMap {
      case DataType.Product(n, _, fs) => fs.map(f => f.ty -> s"the field ${f.name} of ${n.value}")
      case DataType.Sum(_, _, cs)     => cs.toList.flatMap(c => c.fields.map(f => f.ty ->
          s"the field ${f.name} of ${c.name.value}"))
    }
    quantified ++ v.models.map(m => m.state -> s"the state of ${m.name.value}") ++ definitions ++ ops ++ fields
