package frflow.project.port.memory

import cats.Monad
import cats.data.NonEmptyList
import cats.effect.Ref
import cats.syntax.all.*
import frflow.project.port.Prover
import frflow.proof.prover.ast.{ProverModule, ModuleName}
import frflow.proof.reading.{RocqReport, RocqSource}
import frflow.proof.rocq.{RocqNames, RocqProject}
import frflow.proof.verdict.ProverRun

/** The prover scripted: each module's build answered by `answer`, a build of several the worst of their answers (a
  * timeout, else a failure, else built) with their reports joined. `built` is every build asked, in order.
  */
final class ScriptedProver[F[_]: Monad] private (answer: ModuleName => ProverRun, asked: Ref[F, Vector[ModuleName]],
    installed: Boolean) extends Prover[F]:
  def available: F[Boolean] = installed.pure[F]

  def build(targets: NonEmptyList[ModuleName]): F[ProverRun] =
    asked.update(_ ++ targets.toList).as(ScriptedProver.worst(targets.map(answer)))

  def built: F[List[ModuleName]] = asked.get.map(_.toList)

object ScriptedProver:
  def apply[F[_]: Monad: Ref.Make](answer: ModuleName => ProverRun, installed: Boolean): F[ScriptedProver[F]] =
    Ref.of[F, Vector[ModuleName]](Vector.empty).map(new ScriptedProver(answer, _, installed))

  /** A module's build as Rocq would answer of a model whose proofs go through: each lemma of `source` (the module's
    * text) named in `failing`, by its name in the module (`complete`), not accepted, and each other lemma it audits
    * resting on nothing; built when nothing failed.
    */
  def building(m: ProverModule, source: String, failing: Set[String]): ProverRun =
    val named = failing.map(f => RocqNames.joined(m.namespace.map(_.text) :+ f))
    val open = RocqSource.lemmas(source).map(_.name).filter(named)
    val audits = RocqSource.audited(source).filterNot(open.contains).map(_ -> List.empty[String]).toMap
    val report = RocqReport.print(List(RocqReport.File(RocqProject.file(m.name),
      open.map(_ -> "the proof does not go through").toMap, audits, None)))
    if open.isEmpty then ProverRun.Built(report) else ProverRun.Failed(report)

  /** Of a module the script has no text of (one written as the check goes, a step's refutation): built, Rocq having
    * read it to its end.
    */
  def ended(m: ModuleName): ProverRun =
    ProverRun.Built(RocqReport.print(List(RocqReport.File(RocqProject.file(m), Map.empty, Map.empty, None))))

  private def worst(runs: NonEmptyList[ProverRun]): ProverRun =
    val out = runs.map(_.output).toList.mkString
    if runs.exists { case ProverRun.TimedOut(_) => true; case _ => false } then ProverRun.TimedOut(out)
    else if runs.exists { case ProverRun.Failed(_) => true; case _ => false } then ProverRun.Failed(out)
    else ProverRun.Built(out)

  extension (r: ProverRun)
    private def output: String = r match
      case ProverRun.Built(o)    => o
      case ProverRun.Failed(o)   => o
      case ProverRun.TimedOut(o) => o
