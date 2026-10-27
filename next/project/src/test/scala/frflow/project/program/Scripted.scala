package frflow.project.program

import frflow.project.pipeline.Analysis
import frflow.proof.lean.ast.{LeanModule, ModuleName}
import frflow.proof.lean.lower.LowerObligation
import frflow.proof.lean.print.Print
import frflow.proof.obligation.Discharge
import frflow.proof.reading.Elaboration
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
    a.modules.find(_.name == m).fold(ProverRun.Built(""))(module => Scripted.run(module,
      (tries -- proving) ++ failing))

  private def attempt(d: Discharge): Boolean = d match
    case Discharge.Attempt(_) => true
    case _                    => false

object Scripted:
  /** A module's build: Lake's line of its job and an error at each theorem named in `failing` it holds, else built
    * with no message.
    */
  def run(m: LeanModule, failing: Set[String]): ProverRun =
    val file = m.name.file.value.stripPrefix("lean/")
    val errors = Elaboration(Print.module(m), "", file).theorems.filter(t => failing(t.name))
      .map(t => s"error: $file:${t.from}:2: unsolved goals")
    if errors.isEmpty then ProverRun.Built("")
    else ProverRun.Failed((s"✖ [1/1] Building ${m.name.dotted}" :: errors).mkString("\n"))
