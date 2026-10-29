package frflow.api

import cats.effect.IO
import frflow.api.shell.{Memory, Session}
import frflow.decision.ledger.{Deciders, Ledger}
import frflow.project.port.{Lake, ProjectFiles}
import frflow.project.port.memory.{MemoryGit, MemoryKeys, MemoryLedger}
import frflow.project.program.Ports
import frflow.testing.{Seed, Settings}
import java.nio.file.Path

/** The API over a project's files on disk and Lean's `lake`, its ledger, git and key in memory (`ann` listed): a
  * project end to end without a key file, for the ports' walk-throughs. Its tests run today's settings, 1,000 cases
  * from seed 1.
  */
object OnDisk:
  def ports(dir: Path): IO[Ports[IO]] =
    for
      ledger <- MemoryLedger[IO](Ledger.empty)
      git    <- MemoryGit[IO]
      keys   <- MemoryKeys[IO]
      _      <- keys.list(keys.signed(Deciders(List(keys.entry("ann")), None, None)))
    yield Ports(ProjectFiles.make[IO](dir), ledger, git, keys)

  def api(p: Project, ports: Ports[IO], lake: Lake[IO], version: String): IO[FrFlowApi[IO]] =
    Memory.api(Session[IO](p, ports, _ => IO.pure(lake),
      Session.Run(Settings(1000, Seed(1)), Some("ann"), keyed = true), version))
