package frflow.eval.run

import frflow.core.analysis.Resolve
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.spec.{Range, Statement}
import frflow.core.Theory
import frflow.eval.{Env, EvalError, Fn, ScalaValue, Semantics}

/** A fact about the values plain code runs with (an assumption over every possible value that reads as no call),
  * compiled once: the values it reads, and whether it holds under an environment. One that quantifies has no Scala
  * value: it is trusted.
  */
final case class Assumes(id: NodeId, reads: List[SymbolName], formula: Env => Either[EvalError, ScalaValue]):
  def within(bound: Set[SymbolName]): Boolean = reads.forall(bound)
  def holds(env: Env): Boolean = formula(env).fold(_ == EvalError.Quantified, Fn.bool)

object Assumes:
  def of(semantics: Semantics, t: Theory): List[Assumes] = t.nodes.map(_.node).flatMap(n => n.statement match
    case s @ Statement.Assumption(f) if s.stated && s.call.isEmpty && s.range.contains(Range.Possible) =>
      Some(Assumes(n.id, Resolve.mentions(t, n.id).symbols, semantics.formula(f)))
    case _ => None)
