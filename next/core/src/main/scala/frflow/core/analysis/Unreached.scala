package frflow.core.analysis

import frflow.core.expr.{Expr, Exprs, Quantifier}
import frflow.core.spec.Range
import frflow.core.Theory
import frflow.core.ty.{DataType, Ty}
import frflow.core.vocab.SymbolType
import Problem.Place
import frflow.core.analysis.outside.Guards

/** The places a guard of `always[T]` would go but cannot yet (owner §16: an `always` holds wherever FrFlow covers
  * the code): a type holding a `T` (`Scope.holds`) inside a map, a set or a function value, which `Guards` does not
  * walk. A place is a type a statement quantifies over, a store's state, an input or the result of a Definition or an
  * operation on a state, and a field of a domain type. A Definition's own function type is not one (its inputs and result
  * are), nor is a program's result (its `made_` is step 3's).
  */
object Unreached:
  def of(t: Theory): List[Problem] =
    val all = places(t).filter { case (Ty.FlowOf(_, _), _) => false; case _ => true }
    t.nodes.map(_.node).flatMap(n => n.statement.range.toList.flatMap {
      case Range.Made(ty) => all.collect {
          case (x, at) if Scope.holds(t, ty, x) && !Guards.applies(t, ty, x) => Problem.AlwaysNotReached(n.id, x, at)
        }
      case _              => Nil
    }).distinct

  private def places(t: Theory): List[(Ty, Place)] =
    val v = t.vocabulary
    val quantified = t.nodes.map(_.node).flatMap(n => n.statement.said.toList.flatMap(f => Exprs.all(f.value).collect {
      case Expr.Quant(Quantifier.Forall | Quantifier.Exists, xs, _) => xs.map(_.ty -> Place.Variable(n.id))
    }.flatten))
    val definitions = v.symbols.flatMap(s => s.ty match
      case SymbolType.Typed(Ty.FnOf(ins, r)) => ins.map(_ -> Place.Input(s.name.value)) :+
          (r -> Place.Result(s.name.value))
      case SymbolType.Typed(x)               => List(x -> Place.Value(s.name.value))
      case _                                 => Nil)
    val ops = v.models.flatMap(_.sigs).flatMap(o => o.params.map(_._2 -> Place.Input(o.name.value)) :+
      (o.result -> Place.Result(o.name.value)))
    val fields = v.types.flatMap {
      case DataType.Product(n, _, fs) => fs.map(f => f.ty -> Place.Field(f.name, n.value))
      case DataType.Sum(_, _, cs)     =>
        cs.toList.flatMap(c => c.fields.map(f => f.ty -> Place.Field(f.name, c.name.value)))
    }
    quantified ++ v.models.map(m => m.state -> Place.State(m.name)) ++ definitions ++ ops ++ fields
