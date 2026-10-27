package frflow.api.shell

import cats.effect.Ref
import cats.Monad
import cats.syntax.all.*
import frflow.api.Lean
import frflow.project.pipeline.Analysis
import frflow.project.port.{Lake, ScriptedLake}
import frflow.proof.lean.ast.{LeanModule, ModuleName}
import frflow.proof.lean.lower.LowerObligation
import frflow.proof.lean.print.Print
import frflow.proof.obligation.Discharge
import frflow.proof.reading.Elaboration
import frflow.proof.verdict.ProverRun

/** Lean in memory, answering by the analysis's modules as Lean would of a model whose proofs go through: every module
  * built, but an error at each try (none is proven within its budget) and at each theorem named failing, so a module
  * holding one fails to build.
  */
private[api] object ScriptedLean:
  def apply[F[_]: Monad: Ref.Make](lean: Lean): Analysis => F[Lake[F]] = a => lean match
    case Lean.Absent           => ScriptedLake[F](_ => ProverRun.Built(""), installed = false).widen
    case Lean.Proving(failing) => ScriptedLake[F](answer(a, tries(a) ++ failing), installed = true).widen

  private def tries(a: Analysis): Set[String] =
    (a.obligations.flatMap(_.tried).map(_.name) ++ a.whole.collect { case o if attempt(o.discharge) => o.name })
      .map(LowerObligation.name(_).text).toSet

  private def attempt(d: Discharge): Boolean = d match
    case Discharge.Attempt(_) => true
    case _                    => false

  private def answer(a: Analysis, failing: Set[String])(m: ModuleName): ProverRun =
    a.modules.find(_.name == m).fold(ProverRun.Built(""))(run(_, failing))

  /** A module's build: Lake's line of its job and an error at each theorem it holds named in `failing`. */
  private def run(m: LeanModule, failing: Set[String]): ProverRun =
    val file = m.name.file.value.stripPrefix("lean/")
    val errors = Elaboration(Print.module(m), "", file).theorems.filter(t => failing(t.name))
      .map(t => s"error: $file:${t.from}:2: unsolved goals")
    if errors.isEmpty then ProverRun.Built("")
    else ProverRun.Failed((s"✖ [1/1] Building ${m.name.dotted}" :: errors).mkString("\n"))
