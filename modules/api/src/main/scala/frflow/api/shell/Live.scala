package frflow.api.shell

import cats.Parallel
import cats.effect.{Async, Resource}
import cats.syntax.all.*
import fs2.io.process.Processes
import frflow.api.{FrFlowApi, Project}
import frflow.project.port.{Git, KeyRing, LedgerStore, ProjectFiles, RocqLibrary}
import frflow.project.port.rocq.RocqProver
import frflow.project.program.{Config, Ports}
import frflow.testing.report.Seed
import java.nio.file.Path

/** The API over a project's directory: its files on disk, the ledger's file under its lock, `git`, the developer's
  * key, and Rocq in its `rocq/`, one build at a time, with the version of FrFlow's Rocq library the project's
  * proofs load; run as `env` says (`Config`), a fresh seed the time's. The key is `FRFLOW_KEY`, else
  * `.config/frflow/signing.key` under `HOME`, both from `env` only: with neither, there is no key. It is read once when
  * the project is opened (to say whether there is one), then when a decision is signed. The files the model records
  * are made relative to the project's directory (`Relocate`).
  */
private[api] object Live:
  def make[F[_]: Async: Parallel](p: Project, root: Path, env: Map[String, String]): Resource[F, FrFlowApi[F]] =
    given Processes[F] = Processes.forAsync[F]
    val git = Git.make[F](root)
    for
      fresh  <- Resource.eval(Async[F].realTime.map(t => Seed(t.toMillis)))
      library = root.resolve("rocq").resolve(p.library).normalize
      config  = Config.of(env, library, fresh)
      keys    = config.key.fold(KeyRing.keyless[F](git))(KeyRing.make[F](_, git))
      keyed  <- Resource.eval(keys.key.attempt.map(_.isRight))
      ledger <- LedgerStore.file[F](root)
      rocq   <- RocqProver.make[F](root.resolve("rocq"), library, config.rocq)
      lib    <- Resource.eval(RocqLibrary.read[F](library))
      ports   = Ports(ProjectFiles.make[F](root), ledger, git, keys)
      built  <- Resource.eval(Async[F].delay(Path.of("").toAbsolutePath)) // the build's, as `Source.relative`
      moved   = p.copy(model = Relocate(p.model, built, root))
      api    <- Resource.eval(Memory.api(Session[F](moved, ports, _ => rocq.pure[F],
                  Session.Run(config.tests, env.get("FRFLOW_AS"), keyed), lib.version)))
    yield api
