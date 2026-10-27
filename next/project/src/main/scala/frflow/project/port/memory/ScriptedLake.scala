package frflow.project.port.memory

import cats.Monad
import cats.data.NonEmptyList
import cats.effect.Ref
import cats.syntax.all.*
import frflow.project.port.Lake
import frflow.proof.lean.ast.{LeanModule, ModuleName}
import frflow.proof.lean.print.Print
import frflow.proof.reading.Elaboration
import frflow.proof.verdict.ProverRun

/** Lake scripted: each module's build answered by `answer`, a build of several the worst of their answers (a
  * timeout, else a failure, else built) with their outputs joined. `built` is every build asked, in order.
  */
final class ScriptedLake[F[_]: Monad] private (answer: ModuleName => ProverRun, asked: Ref[F, Vector[ModuleName]],
    installed: Boolean) extends Lake[F]:
  def available: F[Boolean] = installed.pure[F]

  def build(targets: NonEmptyList[ModuleName]): F[ProverRun] =
    asked.update(_ ++ targets.toList).as(ScriptedLake.worst(targets.map(answer)))

  def built: F[List[ModuleName]] = asked.get.map(_.toList)

object ScriptedLake:
  def apply[F[_]: Monad: Ref.Make](answer: ModuleName => ProverRun, installed: Boolean): F[ScriptedLake[F]] =
    Ref.of[F, Vector[ModuleName]](Vector.empty).map(new ScriptedLake(answer, _, installed))

  /** A module's build as Lean would answer of a model whose proofs go through: Lake's line of its job, an error at
    * each theorem it holds named in `failing`, and the audit (`#print axioms`) of each other theorem it audits,
    * resting on none; built when nothing failed.
    */
  def building(m: LeanModule, failing: Set[String]): ProverRun =
    val file = m.name.file.value.stripPrefix("lean/")
    val source = Print.module(m)
    val errors = Elaboration(source, "", file).theorems.filter(t => failing(t.name))
      .map(t => s"error: $file:${t.from}:2: unsolved goals")
    val audits = Audited.findAllMatchIn(source).map(_.group(1)).filterNot(n => failing(n.split('.').last))
      .map(n => s"info: $file:1:0: '$n' does not depend on any axioms").toList
    if errors.isEmpty then ProverRun.Built(audits.mkString("\n"))
    else ProverRun.Failed((s"✖ [1/1] Building ${m.name.dotted}" :: errors ++ audits).mkString("\n"))

  private val Audited = """(?m)^#print\s+axioms\s+(\S+)""".r

  private def worst(runs: NonEmptyList[ProverRun]): ProverRun =
    val out = runs.map(_.output).toList.mkString("\n")
    if runs.exists { case ProverRun.TimedOut(_) => true; case _ => false } then ProverRun.TimedOut(out)
    else if runs.exists { case ProverRun.Failed(_) => true; case _ => false } then ProverRun.Failed(out)
    else ProverRun.Built(out)

  extension (r: ProverRun)
    private def output: String = r match
      case ProverRun.Built(o)    => o
      case ProverRun.Failed(o)   => o
      case ProverRun.TimedOut(o) => o
