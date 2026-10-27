package frflow.api.shell

import cats.Parallel
import cats.effect.{Async, Ref}
import cats.syntax.all.*
import frflow.api.{FrFlowApi, Lean, Project}
import frflow.core.name.RelPath
import frflow.decision.ledger.{Deciders, Ledger}
import frflow.project.port.memory.{MemoryFiles, MemoryGit, MemoryKeys, MemoryLedger}
import frflow.project.pipeline.Recorded
import frflow.project.program.Ports
import frflow.testing.{Seed, Settings}

/** The API in memory: the files as given, an empty ledger, a repository with no commit, a key made for the run (the
  * deciders' list holding it under `decider`, as if committed), Lean scripted, and the tests on 200 cases from seed
  * 1, so a run repeats.
  */
private[api] object Memory:
  val Tests: Settings = Settings(200, Seed(1))

  def make[F[_]: Async: Parallel](p: Project[F], files: Map[RelPath, String], decider: Option[String], lean: Lean)
      : F[FrFlowApi[F]] = ports(files, decider).flatMap(ps => api(Session(p, ps, ScriptedLean[F](lean), run)))

  val run: Session.Run = Session.Run(Tests, None, keyed = true)

  def ports[F[_]: Async](files: Map[RelPath, String], decider: Option[String]): F[Ports[F]] =
    for
      f      <- MemoryFiles[F](files)
      ledger <- MemoryLedger[F](Ledger.empty)
      git    <- MemoryGit[F]
      keys   <- MemoryKeys[F]
      _      <- decider.traverse_(name => keys.list(keys.signed(Deciders(List(keys.entry(name)), None, None))))
    yield Ports(f, ledger, git, keys)

  /** The algebras over a session, acceptances decided on what this API checked afresh (`Fresh`). */
  def api[F[_]: Async: Parallel](s: Session[F]): F[FrFlowApi[F]] =
    Ref.of[F, Option[Recorded]](None).map(found => FrFlowApi(Reads(s), Decides(s, Fresh(s, found)), Proves(s)))
