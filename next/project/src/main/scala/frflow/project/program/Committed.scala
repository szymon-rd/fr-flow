package frflow.project.program

import cats.Monad
import cats.syntax.all.*
import frflow.decision.ledger.{Ledger, LedgerBase}
import frflow.project.port.Records
import frflow.wire.file.Files
import frflow.wire.ledger.{LedgerBaseFile, LedgerFile}

/** What of the repository a ledger is counted against: the committed ledger base (`.frflow/ledger-base`, its
  * versions each following the one before and signed by a key the committed deciders' list holds; none when one
  * does not read or follow), and the committed versions of the ledger from the last one the base accepts, each read
  * (none for one that does not read).
  */
object Committed:
  def ledgers[F[_]: Monad](ports: Ports[F]): F[List[Option[Ledger]]] =
    (ports.git.versions(Records.path(LedgerFile.format)), base(ports))
      .mapN((texts, b) => LedgerBase.from(texts, b).map(Files.read(LedgerFile.format, _).toOption))

  def base[F[_]: Monad](ports: Ports[F]): F[Option[LedgerBase]] =
    (ports.git.versions(Records.path(LedgerBaseFile.format)), ports.keys.deciders, ports.keys.verifier)
      .mapN((texts, ds, verify) =>
        texts.traverse(Files.read(LedgerBaseFile.format, _).toOption).flatMap(LedgerBase.committed(_, ds, verify)))
