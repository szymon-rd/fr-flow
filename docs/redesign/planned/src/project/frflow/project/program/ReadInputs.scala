package frflow.project.program

import cats.effect.Clock
import cats.{Monad, Parallel}
import cats.syntax.all.*
import frflow.core.Elaborated
import frflow.core.name.{NodeId, RelPath}
import frflow.project.pipeline.{Inputs, Recorded}
import frflow.project.port.{LedgerStore, ProjectFiles}
import frflow.proof.layout.Layout
import frflow.proof.reading.ProofFile

/** Reading a run's inputs, each once, side by side: the program every operation starts with. It asks only for
  * `Monad`, `Parallel` and `Clock`: it cannot do anything the algebras it is given do not.
  */
final class ReadInputs[F[_]: Monad: Parallel: Clock](files: ProjectFiles[F], ledger: LedgerStore[F],
    recorded: F[Recorded], sourcesDir: RelPath):
  def apply(e: Elaborated): F[Inputs] =
    (ledger.load, recorded, proofs(e), sources, Clock[F].realTimeInstant).parMapN(Inputs.apply)

  private def proofs(e: Elaborated): F[Map[NodeId, ProofFile]] =
    files.list(Layout(e.theory.name).proofsDir).flatMap(_.traverseFilter(p =>
      files.read(p).map(_.map(text => NodeId(p.stem) -> ProofFile(NodeId(p.stem), text))))).map(_.toMap)

  /** The project's Scala sources: the files the nodes are written in, and those they govern (`Governance`). */
  private def sources: F[Map[RelPath, String]] =
    files.list(sourcesDir).flatMap(_.traverseFilter(p => files.read(p).map(_.map(p -> _))))
      .map(_.toMap)
