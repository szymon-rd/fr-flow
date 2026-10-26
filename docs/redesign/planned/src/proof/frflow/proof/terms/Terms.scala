package frflow.proof.terms

import cats.syntax.all.*
import frflow.core.analysis.Resolved
import frflow.core.expr.{Expr, Exprs}
import frflow.core.graph.Edge
import frflow.core.name.{DefName, NodeId}
import frflow.core.spec.Statement

/** The open terms of an expression and of a claim, the defines' terms read from `known` (computed once each). */
final class Terms(r: Resolved, known: Map[DefName, OpenTerms]):
  /** What `e` mentions, and what the defines it calls are over (`self` left out: a recursive define). */
  def of(e: Expr, self: Set[DefName] = Set.empty): OpenTerms =
    val m = Exprs.mentions(e)
    val sorts = m.types.filter(n => r.theory.vocabulary.sorts.exists(_.name == n))
    OpenTerms(sorts, m.symbols) |+| m.defines.filterNot(self).foldMap(d => known.getOrElse(d,
      r.theory.vocabulary.define(d).foldMap(x => of(x.lambda.body, self + d))))

  /** A claim's terms: its formula's; a contract's, its post's (a flow's, with its failure clause's) and its
    * operation; an invariant's, its rule's and every keeper's view and operation.
    */
  def ofClaim(n: NodeId, s: Statement): OpenTerms = s match
    case Statement.Invariant(rule, _)          => of(rule.value.body) |+| keepers(n)
    case Statement.FlowContract(_, p, fail, _) =>
      (p.post.value.body :: fail.toList.flatMap(_.exprs)).foldMap(of(_)) |+| operation(s)
    case other                                 => other.exprs.headOption.foldMap(of(_)) |+| operation(other)

  private def keepers(invariant: NodeId): OpenTerms = r.theory.edges.foldMap {
    case Edge.Keeps(c, `invariant`, view) =>
      of(view.value.body) |+| r.theory.node(c).foldMap(n => operation(n.statement))
    case _                                => OpenTerms.empty
  }

  private def operation(s: Statement): OpenTerms = s.operation.foldMap(o => OpenTerms(Nil, List(o)))
