package frflow.project.program

import frflow.project.pipeline.Analysis
import frflow.project.port.memory.ScriptedProver
import frflow.proof.prover.ast.ModuleName
import frflow.proof.prover.lower.LowerObligation
import frflow.proof.obligation.Discharge
import frflow.proof.verdict.ProverRun

/** What a scripted prover says of an analysis's modules, as Rocq would of a model whose proofs go through: every
  * module read, but each try (tried within its budget) not proven, so a module holding tries does not go through
  * whole. `failing` adds lemmas not proven; `proving` takes tries off the list.
  */
final case class Scripted(a: Analysis, failing: Set[String], proving: Set[String]):
  private val tries: Set[String] =
    (a.obligations.flatMap(_.tried).map(_.name) ++ a.whole.collect { case o if attempt(o.discharge) => o.name })
      .map(LowerObligation.name(_).text).toSet

  def answer(m: ModuleName): ProverRun =
    a.modules.find(_.name == m).flatMap(module => a.rocq.text(m).map(ScriptedProver.building(module, _,
      (tries -- proving) ++ failing))).getOrElse(ScriptedProver.ended(m))

  private def attempt(d: Discharge): Boolean = d match
    case Discharge.Attempt(_) => true
    case _                    => false
