package frflow.proof.terms

import cats.syntax.all.*
import frflow.core.analysis.Resolved
import frflow.core.expr.{Expr, Exprs}
import frflow.core.name.DefName
import frflow.core.spec.Statement

/** The open terms of an expression and of a claim, the defines' terms read from `known` (computed once each). */
final class Terms(r: Resolved, known: Map[DefName, OpenTerms]):
  /** What `e` mentions, and what the defines it calls are over (`self` left out: a recursive define). */
  def of(e: Expr, self: Set[DefName] = Set.empty): OpenTerms =
    val m = Exprs.mentions(e)
    val sorts = m.types.filter(n => r.theory.vocabulary.sorts.exists(_.name == n))
    OpenTerms(sorts, m.symbols) |+| m.defines.filterNot(self).foldMap(d => known.getOrElse(d,
      r.theory.vocabulary.define(d).foldMap(x => of(x.lambda.body, self + d))))

  /** A statement's terms: its formula's, and a run's failure clause's, the Definitions it mentions among them. */
  def ofClaim(s: Statement): OpenTerms = s.exprs.foldMap(of(_))
