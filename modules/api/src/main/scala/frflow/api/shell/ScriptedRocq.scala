package frflow.api.shell

import cats.effect.Ref
import cats.Monad
import cats.syntax.all.*
import frflow.api.Rocq
import frflow.project.pipeline.Analysis
import frflow.project.port.Prover
import frflow.project.port.memory.ScriptedProver
import frflow.proof.prover.ast.ModuleName
import frflow.proof.prover.lower.LowerObligation
import frflow.proof.obligation.Discharge
import frflow.proof.verdict.ProverRun

/** Rocq in memory, answering by the analysis's modules as Rocq would of a model whose proofs go through: every module
  * read, but each try not named shown not accepted (it is not proven within its budget), and each lemma named
  * failing; each other lemma's audit printed (`ScriptedProver.building`).
  */
private[api] object ScriptedRocq:
  def apply[F[_]: Monad: Ref.Make](rocq: Rocq): Analysis => F[Prover[F]] = a => rocq match
    case Rocq.Absent           => ScriptedProver[F](_ => ProverRun.Built(""), installed = false).widen
    case Rocq.Proving(failing, shown) =>
      ScriptedProver[F](answer(a, tries(a) -- shown ++ failing), installed = true).widen

  private def tries(a: Analysis): Set[String] =
    (a.obligations.flatMap(_.tried).map(_.name) ++ a.whole.collect { case o if attempt(o.discharge) => o.name })
      .map(LowerObligation.name(_).text).toSet

  private def attempt(d: Discharge): Boolean = d match
    case Discharge.Attempt(_) => true
    case _                    => false

  private def answer(a: Analysis, failing: Set[String])(m: ModuleName): ProverRun =
    a.modules.find(_.name == m).flatMap(module => a.rocq.text(m).map(ScriptedProver.building(module, _, failing)))
      .getOrElse(ScriptedProver.ended(m))
