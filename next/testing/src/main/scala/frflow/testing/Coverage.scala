package frflow.testing

import cats.syntax.all.*
import frflow.core.consistency.{Conditions, Consistency, Vacuity}
import frflow.core.name.NodeId
import frflow.core.spec.Written.term
import frflow.core.term.Stated
import frflow.core.Theory
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.eval.{Env, Fn, ScalaValue, Semantics}
import frflow.eval.run.Wiring
import frflow.testing.derive.Parts
import frflow.testing.report.{Hits, Position}
import scala.util.Try

/** Which conditions of a claim (each `A` of an `A implies B`) a case meets, each evaluated at the case's variables,
  * every Definition given its meaning. A condition below a further binder (a list's element, `b` of
  * `shelf.forall(b => …)`) is met when some value of the binder's type the case holds meets it: its membership is
  * part of the condition, so an element of the list is found among them.
  */
final class Coverage(semantics: Semantics, t: Theory, node: NodeId, inputs: List[Ty]):
  private val wiring = Wiring(semantics, t)
  private val parts = Parts(t.vocabulary)
  private val formula = t.node(node).flatMap(_.statement.said)

  /** The conditions counted, each with the types of the binders below the case's variables. */
  val conditions: List[(Position, List[Ty])] = Consistency.vacuity(t).collect {
    case Vacuity.Satisfiable(`node`, i, over) if over.take(inputs.size) == inputs =>
      Position(i) -> over.drop(inputs.size)
  }

  def of(c: Case): Hits = conditions.foldMap((p, below) => Hits.of(p, held(p.condition, below, c)))

  private def held(i: Int, below: List[Ty], c: Case): Boolean = formula.exists { f =>
    val env = Env.of(wiring.values(wiring.supplied(c.givens)))
    val at = c.inputs.zip(inputs).map(semantics.literal)
    semantics.term(Stated(Conditions.predicate(f.term, i)))(env).exists(p =>
      combinations(below.map(holding(c, _))).take(Coverage.Budget).exists(vs =>
        Try(Fn.bool((at ++ vs).foldLeft(p)((g, x) => Fn.call(Fn.ref(g), List(x))))).getOrElse(false)))
  }

  /** The values of `ty` the case holds, in its inputs and the values given. */
  private def holding(c: Case, ty: Ty): List[ScalaValue] =
    val values = c.inputs.zip(inputs) ++ c.givens.flatMap(g => t.vocabulary.symbol(g.symbol).map(_.ty).collect {
      case SymbolType.Typed(gt) => g.value -> gt })
    values.flatMap((v, vt) => parts(v, vt)).collect { case (v, `ty`) => v }.distinct.map(semantics.literal(_, ty))

  private def combinations(xss: List[List[ScalaValue]]): Iterator[List[ScalaValue]] = xss match
    case Nil        => Iterator(Nil)
    case xs :: rest => xs.iterator.flatMap(x => combinations(rest).map(x :: _))

object Coverage:
  /** The most values of the binders below a case's variables tried, per condition. */
  val Budget: Int = 200
