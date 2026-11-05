package frflow.api.shell

import cats.effect.Ref
import cats.Monad
import cats.syntax.all.*
import frflow.api.Lean
import frflow.project.pipeline.Analysis
import frflow.project.port.Lake
import frflow.project.port.memory.ScriptedLake
import frflow.proof.lean.ast.ModuleName
import frflow.proof.lean.lower.LowerObligation
import frflow.proof.obligation.Discharge
import frflow.proof.verdict.ProverRun

/** Lean in memory, answering by the analysis's modules as Lean would of a model whose proofs go through: every module
  * built, but an error at each try not named shown (it is not proven within its budget) and at each theorem named
  * failing, so a module holding one fails to build; each other theorem's audit printed (`ScriptedLake.building`).
  */
private[api] object ScriptedLean:
  def apply[F[_]: Monad: Ref.Make](lean: Lean): Analysis => F[Lake[F]] = a => lean match
    case Lean.Absent           => ScriptedLake[F](_ => ProverRun.Built(""), installed = false).widen
    case Lean.Proving(failing, shown) =>
      ScriptedLake[F](answer(a, tries(a) -- shown ++ failing), installed = true).widen

  private def tries(a: Analysis): Set[String] =
    (a.obligations.flatMap(_.tried).map(_.name) ++ a.whole.collect { case o if attempt(o.discharge) => o.name })
      .map(LowerObligation.name(_).text).toSet

  private def attempt(d: Discharge): Boolean = d match
    case Discharge.Attempt(_) => true
    case _                    => false

  private def answer(a: Analysis, failing: Set[String])(m: ModuleName): ProverRun =
    a.modules.find(_.name == m).fold(ProverRun.Built(""))(ScriptedLake.building(_, failing))
