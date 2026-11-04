package frflow.api

import cats.Parallel
import cats.effect.{Async, Resource}
import cats.effect.Sync
import frflow.api.shell.{Listing, Live, Memory}
import frflow.api.view.Listed
import frflow.core.name.RelPath
import java.nio.file.Path

/** FrFlow as a front end sees it. Interpreters: the live one over a project's directory, the in-memory one the front
  * ends test on. What an operation cannot go on from is raised as a `view.Stop`.
  */
final case class FrFlowApi[F[_]](reading: Reading[F], deciding: Deciding[F], proving: Proving[F])

object FrFlowApi:
  /** The project at `root`, held for the life of the resource (the ledger's lock, one `lake` build at a time), run as
    * `env` says: `FRFLOW_LAKE`, `FRFLOW_KEY`, `FRFLOW_SEED`, `FRFLOW_AS`, and `HOME` for the default key.
    */
  def make[F[_]: Async: Parallel](p: Project, root: Path, env: Map[String, String]): Resource[F, FrFlowApi[F]] =
    Live.make[F](p, root, env)

  /** The project in memory: its files as given, an empty ledger, a repository with no commit, a key made for the run
    * (listed in the committed deciders' list under `decider`, when given), and Lean as `lean` says.
    */
  def inMemory[F[_]: Async: Parallel](p: Project, files: Map[RelPath, String], decider: Option[String], lean: Lean)
      : F[FrFlowApi[F]] = Memory.make[F](p, files, decider, lean)

  /** The first deciders' list of the project at `root`: the developer's key (as `env` names it, as `make` reads it)
    * listed under `name` and sealed by it, written to `.frflow/deciders` unless a list is there; no key raises
    * `Stop.NoKey`. The developer's own act (`init --as NAME`): commit the list, since only committed versions count.
    */
  def firstDecider[F[_]: Sync](root: Path, name: String, env: Map[String, String]): F[Listed] =
    Listing.first(root, name, env)
