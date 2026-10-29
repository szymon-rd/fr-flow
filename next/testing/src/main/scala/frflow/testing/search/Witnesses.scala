package frflow.testing.search

import frflow.core.code.Values
import frflow.core.consistency.{Conditions, Consistency, Vacuity}
import frflow.core.expr.Value
import frflow.core.name.{DefName, NodeId, SymbolName}
import frflow.core.term.Stated
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.core.Theory
import frflow.eval.run.Wiring
import frflow.eval.{Env, Fn, NotEvaluated, ScalaValue, Semantics}

/** The values that show what always holds possible and each condition able to hold (owner §18), found by a search:
  * first what the FrModel's generators draw (`drawn`), then the small values of each type (`Small`), each
  * judged by the evaluator; the first that holds, in order, so the search is deterministic. A witness Lean is then
  * given (`proof.obligation.Joint`); none found leaves the statement "not shown".
  */
final class Witnesses(semantics: Semantics, t: Theory, drawn: Ty => List[Value]):
  private val small = Small(t.vocabulary)

  def of(v: Vacuity): Option[List[(Value, Ty)]] = v match
    case Vacuity.Inhabited(n, ty)        =>
      candidates(ty).find(x => Consistency.meets(t, n, ty).forall(holds(_, x, ty))).map(x => List(x -> ty))
    case Vacuity.Satisfiable(n, i, over) => Consistency.condition(t, n, i).flatMap { c =>
      val opens = Consistency.opens(t, c)
      val types = opens.map(typeOf) ++ over
      combinations(types.map(candidates)).take(Witnesses.Budget)
        .find(vs => satisfies(n, i, opens, vs.zip(types).map(semantics.literal))).map(_.zip(types))
    }

  private def candidates(ty: Ty): List[Value] = (drawn(ty) ++ small.of(ty)).distinct

  /** A rule's define (an `always[T]`'s, named as its node, or a store's start), at `x`. */
  private def holds(rule: DefName, x: Value, ty: Ty): Boolean =
    t.vocabulary.define(rule).exists(d =>
      semantics.lambda(d.written).run(Env.of(Values.none), List(semantics.literal(x, ty))).exists(Fn.bool))

  /** The condition's predicate, the open values bound, applied to the variables' values; a candidate the predicate
    * has no Scala value at (a quantifier over a whole type inside it) meets nothing.
    */
  private def satisfies(n: NodeId, i: Int, opens: List[SymbolName], literals: List[ScalaValue]): Boolean =
    t.node(n).flatMap(_.statement.said).exists { f =>
      val opened = Values(opens.zip(literals).map((s, v) => s -> (() => v.unwrap)).toMap)
      val env = Env.of(Wiring.onModels(semantics, t).values(opened))
      semantics.term(Stated(Conditions.predicate(f.term, i)))(env).exists(p =>
        try Fn.bool(literals.drop(opens.size).foldLeft(p)((g, x) => Fn.call(Fn.ref(g), List(x))))
        catch case _: NotEvaluated => false)
    }

  private def typeOf(s: SymbolName): Ty =
    t.vocabulary.symbol(s).map(_.ty).collect { case SymbolType.Typed(ty) => ty }.getOrElse(Ty.Never)

  /** Every combination of one value per list, the first list varying slowest. */
  private def combinations(xss: List[List[Value]]): Iterator[List[Value]] = xss match
    case Nil       => Iterator(Nil)
    case xs :: rest => xs.iterator.flatMap(x => combinations(rest).map(x :: _))

object Witnesses:
  val Budget: Int = 5000
