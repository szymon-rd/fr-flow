package frflow.project.program

import frflow.project.pipeline.Analysis
import frflow.project.port.memory.ScriptedLake
import frflow.proof.lean.ast.ModuleName
import frflow.proof.lean.lower.LowerObligation
import frflow.proof.obligation.Discharge
import frflow.proof.verdict.ProverRun

/** What a scripted Lake says of an analysis's modules, as Lean would of a model whose proofs go through: every
  * module built, but that each try (tried within its budget) is not proven, an error at its theorem, so a module
  * holding tries fails to build. `failing` adds theorems not proven; `proving` takes tries off the list.
  */
final case class Scripted(a: Analysis, failing: Set[String], proving: Set[String]):
  private val tries: Set[String] =
    (a.obligations.flatMap(_.tried).map(_.name) ++ a.whole.collect { case o if attempt(o.discharge) => o.name })
      .map(LowerObligation.name(_).text).toSet

  def answer(m: ModuleName): ProverRun =
    a.modules.find(_.name == m).fold(ProverRun.Built(""))(module => ScriptedLake.building(module,
      (tries -- proving) ++ failing))

  private def attempt(d: Discharge): Boolean = d match
    case Discharge.Attempt(_) => true
    case _                    => false
