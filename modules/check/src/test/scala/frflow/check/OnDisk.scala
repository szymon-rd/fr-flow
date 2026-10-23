package frflow
package check

import cats.effect.IO
import cats.syntax.all.*
import frflow.ledger.*
import frflow.protocol.*

/** A knowledge base in a workspace on disk, read, decided and checked as the API does it (unsigned). */
final class OnDisk private (val kb: KnowledgeBase, val ws: Workspace, val cfg: Config, val lake: Lake, ledger: JsonStore[Ledger]):
  def analysis: IO[Analysis] = Analysis.read(kb, ws, cfg, ledger)
  /** The nodes checked, and the analysis with them recorded. */
  def check(only: Option[String] = None): IO[(List[(Node[?], NodeCheck)], Analysis)] = analysis.flatMap(CheckRunner.check(_, lake, cfg, only))
  def decide(d: Decide): IO[Either[Refusal, Unit]] =
    (analysis, IO.realTimeInstant).flatMapN((a, now) => ledger.update(l => Decide(a.snapshot, l, d, "dev", Stamp(now)).map(_ -> ())))

object OnDisk:
  def apply(kb: KnowledgeBase, ws: Workspace): IO[OnDisk] =
    for
      cfg <- Config.load
      lake <- Lake(ws.lean, cfg)
      ledger <- JsonStore.make(ws.ledgerFile, Ledger.empty)
    yield new OnDisk(kb, ws, cfg, lake, ledger)

  /** What `status` passes: every node accepted and proven, and nothing to warn of. */
  def ok(a: Analysis): Boolean = Proofs.complete(a.annotated) && a.warnings.isEmpty
