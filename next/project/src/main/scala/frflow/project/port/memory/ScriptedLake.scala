package frflow.project.port.memory

import cats.Monad
import cats.data.NonEmptyList
import cats.effect.Ref
import cats.syntax.all.*
import frflow.project.port.Lake
import frflow.proof.lean.ast.ModuleName
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
