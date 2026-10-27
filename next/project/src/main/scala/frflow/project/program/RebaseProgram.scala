package frflow.project.program

import cats.Monad
import cats.syntax.all.*
import frflow.decision.ledger.LedgerBase
import frflow.decision.rules.Refusal
import frflow.project.port.Records
import frflow.wire.file.Files
import frflow.wire.ledger.{LedgerBaseFile, LedgerFile}

/** `rebase`: the ledger as it reads now accepted as the start of its committed history, refused unless the key at
  * hand is listed under `by` in the committed deciders' list. Under the ledger's lock its file is written again as
  * FrFlow writes it (a merge's text becomes the canonical one), and `.frflow/ledger-base` names that text's hash and
  * the committed base before it, sealed by the key. It counts once both files are committed.
  */
final class RebaseProgram[F[_]: Monad](ports: Ports[F]):
  def apply(by: String): F[Either[Refusal, LedgerBase]] =
    (ports.keys.deciders, ports.keys.key).tupled.flatMap { (ds, key) =>
      if !ds.exists(_.allows(by, key)) then Refusal.NotADecider(by).asLeft[LedgerBase].pure[F]
      else
        for
          ledger <- ports.ledger.update(l => (l, l).asRight[Refusal])
          before <- Committed.base(ports)
          sign   <- ports.keys.signer
          base    = ledger.map(l => LedgerBase.of(Files.print(LedgerFile.format, l), before))
                      .map(b => b.copy(seal = Some(sign(b.payload))))
          _      <- base.traverse_(b => ports.files.writeIfChanged(Records.path(LedgerBaseFile.format),
                      Files.print(LedgerBaseFile.format, b)))
        yield base
    }
