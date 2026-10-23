package frflow
package check

import cats.effect.IO
import cats.effect.syntax.all.*
import cats.syntax.all.*
import frflow.ledger.*
import frflow.protocol.{NodeKind as _, *}
import io.circe.syntax.*
import java.nio.file.Path

/** A check's results, and the analysis with them recorded (what `status` reads next). */
final case class Checked(results: List[(Node[?], NodeCheck)], after: Analysis):
  def allProven: Boolean = results.forall(_._2.status == CheckStatus.Proven)

/** What CI runs: check (a node whose formal parts did not change keeps its result), then status. */
final case class Ci(checked: Checked, status: Status):
  def ok: Boolean = status.ok && checked.allProven

/** The operations on one knowledge base in its workspace. Each reads the workspace once (`Inputs`),
  * computes (`Analysis`), and writes what it changed.
  */
final class Workflow private (val kb: KnowledgeBase, val ws: Workspace, val cfg: Config, val lake: Lake):

  /** The workspace as it is now, analysed. */
  def analysis: IO[Analysis] = Inputs.read(kb, ws, cfg).map(Analysis(kb, ws, _))

  /** Writes the generated Lean; returns the files that changed. */
  def render: IO[List[String]] = analysis.flatMap(render)

  def render(a: Analysis): IO[List[String]] =
    val g = a.generate
    val keep = a.files.keySet.map(ws.lean.resolve(_).normalize)
    for
      _ <- Disk.update(ws.lean.resolve("lakefile.toml"), g.lakefile(ws.kernelPath))
      _ <- Disk.update(ws.lean.resolve("lean-toolchain"), "leanprover/lean4:v4.35.0\n")
      changed <- a.files.toList.sortBy(_._1).parTraverseN(8)((rel, text) => Disk.update(ws.lean.resolve(rel), text).map(Option.when(_)(rel)))
      stale <- g.generatedDirs.map(ws.lean.resolve).flatTraverse(d => Disk.isDirectory(d).ifM(Disk.files(d), IO.pure(Nil)))
      _ <- stale.filterNot(p => keep(p.normalize)).traverse_(Disk.delete)
    yield changed.flatten

  /** Checks nodes (all, or one), parts first, and records the results. */
  def check(only: Option[String] = None): IO[Checked] =
    for
      a <- analysis
      _ <- render(a)
      results <- CheckRunner.run(CheckPlan(a, only), lake, cfg.threads)
      all = a.checks.filter((id, _) => kb.node(id.value).isDefined) ++ results.map((n, c) => NodeId(n.id) -> c)
      _ <- ChecksStore(ws.checksFile).save(all)
    yield Checked(results, a.withInputs(a.inputs.copy(checks = all)))

  /** Where the knowledge base stands (see `Status.text` for what `status` prints). */
  def status: IO[Status] = analysis.map(Status.of)

  def ci: IO[Ci] = check().map(c => Ci(c, Status.of(c.after)))

  /** Everything known about a node (see `Context`; `Context.text` is what `context` prints). */
  def context(n: Node[?]): IO[Context] =
    (analysis, requests).parTupled.flatMap((a, rs) => codeDiff(a, n).map(Context.of(a, n, rs, _)))

  // How the code a node governs changed since it was decided: a git diff, or "".
  private def codeDiff(a: Analysis, n: Node[?]): IO[String] =
    val id = NodeId(n.id)
    if !a.annotated.byId.get(id).exists(_.review.causes.contains(Cause.Code)) then IO.pure("")
    else IO.blocking {
      val since = a.ledger.binding(id).flatMap(d => d.tree.filter(Git.has(ws.root, _)).orElse(d.commit)).getOrElse("")
      a.code(n).fold("")(c => Git.diff(ws.root, since, c.files))
    }

  /** Creates or extends the proof file of a node with a stub for each open obligation; the file written. */
  def scaffold(n: Node[?]): IO[Option[String]] = analysis.flatMap(Scaffold(_, lake, n))

  /** Writes the snapshot to `.frflow/kb.json`. */
  def writeSnapshot(a: Analysis): IO[Path] =
    Disk.replace(ws.snapshotFile, Canonical.file(a.snapshot.asJson) + "\n").as(ws.snapshotFile)

  def writeSnapshot: IO[Path] = analysis.flatMap(writeSnapshot)

  /** Applies a decision (see `Decisions.decide`) to a fresh snapshot and records it: for programs and tests. */
  def decide(r: DecisionRequest): IO[Either[String, Unit]] =
    def known(s: String) = Option(s).filter(_.nonEmpty)
    for
      a <- analysis
      files = kb.nodes.flatMap(a.code).flatMap(_.files).distinct
      head <- IO.blocking(Git.head(ws.root))
      tree <- IO.blocking(Git.snapshot(ws.root, files))
      at <- IO.realTimeInstant
      decided = Decisions.decide(a.snapshot, a.ledger, r, at.toString, known(head), known(tree))
      _ <- decided.traverse_(l => IO.blocking(LedgerStore.save(ws.ledgerFile, l)))
    yield decided.void

  /** The developer's requests, and the agent's answers. */
  def requests: IO[List[Request]] = IO.blocking(RequestStore.load(ws.requestsFile))

  /** The developer's open requests. */
  def openRequests: IO[List[Request]] = requests.map(_.filter(_.status == RequestStatus.Open))

object Workflow:
  def apply(kb: KnowledgeBase, ws: Workspace): IO[Workflow] = Config.load.flatMap(apply(kb, ws, _))

  def apply(kb: KnowledgeBase, ws: Workspace, cfg: Config): IO[Workflow] =
    Lake(ws.lean, cfg).map(new Workflow(kb, ws, cfg, _))
