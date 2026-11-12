package frflow.api.shell

import cats.Parallel
import cats.effect.Async
import cats.syntax.all.*
import frflow.api.Project
import frflow.api.derive.Derive
import frflow.api.view.{View, Warning}
import frflow.project.pipeline.Analysis
import frflow.project.port.{KeyRing, Prover, RocqLibrary, RunCode}
import frflow.project.program.{Analyse, Committed, Ports, Project as Sources}
import frflow.testing.Settings

/** A project open in the shell: its model, the algebras it is read and written through, the prover each check is
  * run on (given the analysis, so the in-memory one answers by the model's modules), how it runs, and the version of
  * FrFlow's Rocq library its checks are made with (read from disk by the live shell). Each operation analyses the
  * project afresh (its files may have moved), the shell's errors raised as `Stop`s; the developer's code runs on the
  * blocking pool (`RunCode`).
  */
private[api] final class Session[F[_]: Async: Parallel](val project: Project, val ports: Ports[F],
    val prover: Analysis => F[Prover[F]], val run: Session.Run, version: String = Session.InMemory):
  val code: RunCode[F] = RunCode.make[F]
  val library: RocqLibrary = RocqLibrary(project.library, version)
  def analysis: F[Analysis] =
    Analyse(ports, code, Sources(project.sources, run.tests, library))(project.model, project.examples)
      .adaptError(Stops.of)

  def view(a: Analysis): F[View] = warnings.map(Derive.of(a, _))

  /** What the shell warns of besides the analysis: no key to decide with (as found when the project was opened), a
    * deciders' list in the working tree that is not the committed one, and the classes of examples not made.
    */
  private def warnings: F[List[Warning]] =
    (uncommitted(KeyRing.path), uncommitted(Committed.basePath), Committed.taken(ports)).mapN((deciders, base, taken) =>
      Option.unless(run.keyed)(Warning.NoKey).toList ++ Option.when(deciders)(Warning.DecidersUncommitted).toList ++
        Option.when(base || taken.contains(false))(Warning.BaseNotCommitted).toList ++
        project.unread.map(Warning.ExamplesNotRead(_, _)))

  /** A file in the working tree that is not as committed. */
  private def uncommitted(p: frflow.core.name.RelPath): F[Boolean] =
    (ports.files.read(p), ports.git.committed(p)).mapN((now, at) => now.isDefined && now != at)

  /** Raised in `F`, as a front end sees it. */
  def guarded[A](fa: F[A]): F[A] = fa.adaptError(Stops.of)

private[api] object Session:
  /** The library's version where no library is read: the in-memory shell's, whose Rocq is scripted. */
  val InMemory: String = "in memory"

  /** How it runs: the tests' cases and seed, who decides when no one is named (`FRFLOW_AS`), and whether there is a
    * key to decide with.
    */
  final case class Run(tests: Settings, as: Option[String], keyed: Boolean)
