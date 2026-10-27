package frflow.api.shell

import cats.Parallel
import cats.effect.{Async, Resource}
import cats.syntax.all.*
import fs2.io.process.Processes
import frflow.api.{FrFlowApi, Project}
import frflow.project.port.{Git, KeyRing, Lake, LedgerStore, ProjectFiles}
import frflow.project.program.{Config, Ports}
import frflow.testing.Seed
import java.nio.file.Path

/** The API over a project's directory: its files on disk, the ledger's file under its lock, `git`, the developer's
  * key (read only, when a decision is signed), and `lake` in its `lean/`, one build at a time; run as `env` says
  * (`Config`), a fresh seed the time's.
  */
private[api] object Live:
  def make[F[_]: Async: Parallel](p: Project[F], root: Path, env: Map[String, String]): Resource[F, FrFlowApi[F]] =
    given Processes[F] = Processes.forAsync[F]
    for
      home   <- Resource.eval(Async[F].delay(Path.of(env.getOrElse("HOME", System.getProperty("user.home")))))
      fresh  <- Resource.eval(Async[F].realTime.map(t => Seed(t.toMillis)))
      config  = Config.of(env, home, p.library, fresh)
      git     = Git.make[F](root)
      ledger <- LedgerStore.file[F](root)
      lake   <- Lake.make[F](root.resolve("lean"), config.lake)
      ports   = Ports(ProjectFiles.make[F](root), ledger, git, KeyRing.make[F](config.key, git))
    yield Memory.api(Session(p, ports, _ => lake.pure[F], Session.Run(config.tests, env.get("FRFLOW_AS"))))
