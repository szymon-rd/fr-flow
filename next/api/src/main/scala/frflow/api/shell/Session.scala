package frflow.api.shell

import cats.Parallel
import cats.effect.Async
import cats.syntax.all.*
import frflow.api.Project
import frflow.api.derive.Derive
import frflow.api.view.{View, Warning}
import frflow.eval.Semantics
import frflow.project.pipeline.Analysis
import frflow.project.port.{KeyRing, Lake, LeanLibrary, RunCode}
import frflow.project.program.{Analyse, ModelCheck, Ports, Project as Sources}
import frflow.testing.Settings

/** A project open in the shell: its model, the algebras it is read and written through, the Lean each check is run
  * on (given the analysis, so the in-memory Lean answers by the model's modules), how it runs, and the version of
  * FrFlow's Lean library its checks are made with (read from disk by the live shell). Each operation analyses the
  * project afresh (its files may have moved), the shell's errors raised as `Stop`s; the developer's code runs on the
  * blocking pool (`RunCode`).
  */
private[api] final class Session[F[_]: Async: Parallel](val project: Project[F], val ports: Ports[F],
    val lean: Analysis => F[Lake[F]], val run: Session.Run, version: String = Session.InMemory):
  val code: RunCode[F] = RunCode.make[F]
  val library: LeanLibrary = LeanLibrary(project.library, version)
  def models: List[ModelCheck[F]] =
    project.adapters.flatMap(_.tests.of(Semantics(project.model), project.model.theory))

  def analysis: F[Analysis] =
    Analyse(ports, code, Sources(project.sources, run.tests, library))(project.model, project.examples)
      .adaptError(Stops.of)

  def view(a: Analysis): F[View] = warnings.map(Derive.of(a, _))

  /** What the shell warns of besides the analysis: no key to decide with, and a deciders' list in the working tree
    * that is not the committed one.
    */
  private def warnings: F[List[Warning]] =
    val noKey = ports.keys.key.attempt.map(k => Option.when(k.isLeft)(Warning.NoKey))
    val uncommitted = (ports.files.read(KeyRing.path), ports.git.committed(KeyRing.path)).mapN((now, at) =>
      Option.when(now.isDefined && now != at)(Warning.DecidersUncommitted))
    (noKey, uncommitted).mapN((a, b) => a.toList ++ b.toList)

  /** Raised in `F`, as a front end sees it. */
  def guarded[A](fa: F[A]): F[A] = fa.adaptError(Stops.of)

private[api] object Session:
  /** The library's version where no library is read: the in-memory shell's, whose Lean is scripted. */
  val InMemory: String = "in memory"

  /** How it runs: the tests' cases and seed, and who decides when no one is named (`FRFLOW_AS`). */
  final case class Run(tests: Settings, as: Option[String])
