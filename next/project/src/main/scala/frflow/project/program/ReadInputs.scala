package frflow.project.program

import cats.effect.Clock
import cats.{Monad, Parallel}
import cats.syntax.all.*
import frflow.core.Elaborated
import frflow.core.name.{NodeId, RelPath}
import frflow.decision.ledger.{Counted, Ledger}
import frflow.project.pipeline.Inputs
import frflow.project.port.Records
import frflow.proof.layout.Layout
import frflow.proof.reading.ProofFile
import frflow.testing.Settings
import frflow.wire.file.Files
import frflow.wire.ledger.LedgerFile

/** Reading a run's inputs, each once, side by side: the program every operation starts with. The ledger is read as
  * it counts: against the committed deciders' list, and against the ledger as committed (a node whose committed
  * history is not where its history now starts counts none of it). It asks only for `Monad`, `Parallel` and
  * `Clock`: it cannot do anything the algebras it is given do not.
  */
final class ReadInputs[F[_]: Monad: Parallel: Clock](ports: Ports[F], sources: List[RelPath], settings: Settings):
  def apply(e: Elaborated): F[Inputs] =
    (counted, Records.read(ports.files), proofs(e), read, Clock[F].realTimeInstant)
      .parMapN(Inputs(_, _, _, _, _, settings))

  private def counted: F[Counted] =
    (ports.ledger.load, ports.keys.deciders, ports.keys.verifier, committed).parMapN(Counted.of)

  private def committed: F[Option[Ledger]] =
    ports.git.committed(Records.path(LedgerFile.format)).map(_.flatMap(Files.read(LedgerFile.format, _).toOption))

  /** The proof files under `lean/Proofs/<KB>/`, each by its node (the shared lemmas' as `Lemmas`). */
  private def proofs(e: Elaborated): F[Map[NodeId, ProofFile]] =
    ports.files.list(Layout(e.theory.name).proofsDir).flatMap(_.filter(_.value.endsWith(".lean")).traverseFilter(p =>
      ports.files.read(p).map(_.map(text => NodeId(p.stem) -> ProofFile(NodeId(p.stem), text))))).map(_.toMap)

  /** The files under each source directory given: those the nodes are written in, and those they govern
    * (`Governance`).
    */
  private def read: F[Map[RelPath, String]] =
    sources.flatTraverse(ports.files.list).map(_.distinct)
      .flatMap(_.traverseFilter(p => ports.files.read(p).map(_.map(p -> _)))).map(_.toMap)
