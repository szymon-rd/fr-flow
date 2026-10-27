package frflow.api.shell

import cats.Parallel
import cats.effect.{Async, Resource}
import cats.syntax.all.*
import fs2.io.process.Processes
import frflow.api.{FrFlowApi, Project}
import frflow.project.port.{Git, KeyRing, Lake, LeanLibrary, LedgerStore, ProjectFiles}
import frflow.project.program.{Config, Ports}
import frflow.testing.Seed
import java.nio.file.Path

/** The API over a project's directory: its files on disk, the ledger's file under its lock, `git`, the developer's
  * key, and `lake` in its `lean/`, one build at a time, with the version of FrFlow's Lean library the project
  * requires; run as `env` says (`Config`), a fresh seed the time's. The key is `FRFLOW_KEY`, else
  * `.config/frflow/signing.key` under `HOME`, both from `env` only: with neither, there is no key. It is read once when
  * the project is opened (to say whether there is one), then when a decision is signed.
  */
private[api] object Live:
  def make[F[_]: Async: Parallel](p: Project[F], root: Path, env: Map[String, String]): Resource[F, FrFlowApi[F]] =
    given Processes[F] = Processes.forAsync[F]
    val git = Git.make[F](root)
    val keys = keyFile(env).fold[KeyRing[F]](Keyless(KeyRing.make[F](root, git)))(KeyRing.make[F](_, git))
    for
      fresh  <- Resource.eval(Async[F].realTime.map(t => Seed(t.toMillis)))
      // The key is not `Config`'s (its default is under a home `env` may not give): `root` stands for that home.
      config  = Config.of(env, root, Session.library(p), fresh)
      keyed  <- Resource.eval(keys.key.attempt.map(_.isRight))
      ledger <- LedgerStore.file[F](root)
      lake   <- Lake.make[F](root.resolve("lean"), config.lake)
      lib    <- Resource.eval(LeanLibrary.read[F](root.resolve("lean").resolve(Session.library(p)).normalize,
                  Session.library(p)))
      ports   = Ports(ProjectFiles.make[F](root), ledger, git, keys)
    yield Memory.api(Session(p, ports, _ => lake.pure[F], Session.Run(config.tests, env.get("FRFLOW_AS"), keyed),
      lib.version))

  /** `FRFLOW_KEY`, else the default under `HOME`; none when `env` gives neither. */
  def keyFile(env: Map[String, String]): Option[Path] =
    env.get("FRFLOW_KEY").map(_.trim).filter(_.nonEmpty).map(Path.of(_))
      .orElse(env.get("HOME").map(h => Path.of(h).resolve(".config/frflow/signing.key")))
