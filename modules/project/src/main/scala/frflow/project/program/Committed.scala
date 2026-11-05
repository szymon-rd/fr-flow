package frflow.project.program

import cats.Monad
import cats.syntax.all.*
import frflow.core.name.RelPath
import frflow.decision.ledger.{Ledger, LedgerBase}
import frflow.project.port.Records
import frflow.wire.file.Files
import frflow.wire.ledger.{LedgerBaseFile, LedgerFile}

/** What of the repository a ledger is counted against: the committed ledger base (`.frflow/ledger-base`: its versions
  * each following the one before, each signed by a key some committed deciders' list held, the newest by a key the
  * list that counts now holds; none when one does not read or follow), and the committed versions of the ledger from
  * the commit that made that base, when that commit holds the ledger text the base names; all of them otherwise. Each
  * version is read (none for one that does not read).
  */
object Committed:
  val ledgerPath: RelPath = Records.path(LedgerFile.format)
  val basePath: RelPath = Records.path(LedgerBaseFile.format)

  def ledgers[F[_]: Monad](ports: Ports[F]): F[List[Option[Ledger]]] =
    (commits(ports), base(ports)).mapN((cs, b) => b.fold(LedgerBase.texts(cs))(LedgerBase.from(cs, _)._1)
      .map(Files.read(LedgerFile.format, _).toOption))

  def base[F[_]: Monad](ports: Ports[F]): F[Option[LedgerBase]] =
    (ports.git.versions(basePath), ports.keys.lists, ports.keys.deciders, ports.keys.verifier)
      .mapN((texts, lists, now, verify) => texts.traverse(Files.read(LedgerBaseFile.format, _).toOption)
        .flatMap(LedgerBase.committed(_, lists, now, verify)))

  /** Whether the base that counts takes: its commit holds the ledger text it names (none without a base). */
  def taken[F[_]: Monad](ports: Ports[F]): F[Option[Boolean]] =
    (commits(ports), base(ports)).mapN((cs, b) => b.map(LedgerBase.from(cs, _)._2))

  /** Each commit touching the ledger or its base, oldest first: the base it holds, read, and the ledger's text. */
  private def commits[F[_]: Monad](ports: Ports[F]): F[List[(Option[LedgerBase], Option[String])]] =
    ports.git.history(List(ledgerPath, basePath)).map(_.map((_, files) =>
      (files.get(basePath).flatMap(Files.read(LedgerBaseFile.format, _).toOption), files.get(ledgerPath))))
