package frflow.eval.run

import frflow.core.analysis.Resolve
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.spec.Statement
import frflow.core.Theory
import frflow.eval.{Compiled, Denote, Env, EvalError, Fn}

/** A fact about the values plain code runs with, compiled once: the symbols it reads, and whether it holds under an
  * environment. One that quantifies has no Scala value: it is trusted, as today.
  */
final case class Assumes(id: NodeId, reads: List[SymbolName], formula: Compiled):
  def within(bound: Set[SymbolName]): Boolean = reads.forall(bound)
  def holds(env: Env): Boolean = formula.run(env).fold(_ == EvalError.Quantified, Fn.bool)

object Assumes:
  def of(denote: Denote, t: Theory): List[Assumes] = t.nodes.map(_.node).flatMap(n => n.statement match
    case Statement.Fact(f) => Some(Assumes(n.id, Resolve.mentions(t, n.id).symbols, denote(f.value)))
    case _                 => None)
