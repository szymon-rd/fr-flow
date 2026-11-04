package frflow.project.program

import cats.effect.Clock
import cats.{Monad, Parallel}
import cats.syntax.all.*
import frflow.core.Elaborated
import frflow.core.name.{NodeId, RelPath}
import frflow.decision.ledger.{Counted, Ledger}
import frflow.project.pipeline.{Inputs, LeanSources}
import frflow.project.port.Records
import frflow.proof.layout.Layout
import frflow.proof.reading.ProofFile

/** Reading a run's inputs, each once, side by side: the program every operation starts with. The ledger is read as
  * it counts: against the committed deciders' list, and against every committed version of the ledger (a node whose
  * history in one is not where its history in the next, or now, starts counts none of it; a version that does not
  * read counts nothing). It asks only for `Monad`, `Parallel` and `Clock`: it cannot do anything the algebras it is
  * given do not.
  */
final class ReadInputs[F[_]: Monad: Parallel: Clock](ports: Ports[F], project: Project):
  def apply(e: Elaborated): F[Inputs] =
    (counted, Records.read(ports.files), lean(e), read, Clock[F].realTimeInstant)
      .parMapN(Inputs(_, _, _, _, _, project.settings))

  private def counted: F[Counted] =
    (ports.ledger.load, ports.keys.deciders, ports.keys.verifier, committed).parMapN(Counted.of)

  /** Each committed version of the ledger from its base, oldest first; none for one that does not read. */
  private def committed: F[List[Option[Ledger]]] = Committed.ledgers(ports)

  /** The proof files, each `lean/Proofs/<Model>/<Node>.lean` directly in that directory, named by an identifier; every
    * other `.lean` file under `lean/Proofs/` a stray.
    */
  private def lean(e: Elaborated): F[LeanSources] =
    val dir = Layout(e.theory.name).proofsDir
    ports.files.list(RelPath.fromIdentifiers("lean", "Proofs")).map(_.filter(_.value.endsWith(".lean")))
      .flatMap { all =>
        val (proofs, strays) = all.partition(p => ReadInputs.Identifier.matches(p.stem) &&
          p == RelPath.fromIdentifiers(dir.value, s"${p.stem}.lean"))
        proofs.traverseFilter(p => ports.files.read(p).map(_.map(t => NodeId(p.stem) -> ProofFile(NodeId(p.stem), t))))
          .map(found => LeanSources(found.toMap, strays, project.library.version))
      }

  /** The files under each source directory given: those the nodes are written in, and those they govern
    * (`Governance`).
    */
  private def read: F[Map[RelPath, String]] =
    project.sources.flatTraverse(ports.files.list).map(_.distinct)
      .flatMap(_.traverseFilter(p => ports.files.read(p).map(_.map(p -> _)))).map(_.toMap)

object ReadInputs:
  /** A node's id, as a proof file is named. */
  val Identifier: scala.util.matching.Regex = """[A-Za-z_][A-Za-z0-9_]*""".r
