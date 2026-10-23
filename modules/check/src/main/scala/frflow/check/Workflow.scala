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
final class Workflow private (val kb: KnowledgeBase, val ws: Workspace, val cfg: Config, val lake: Lake, val stores: Workflow.Stores):

  /** The workspace as it is now, analysed. */
  def analysis: IO[Analysis] = Inputs.read(kb, ws, cfg, stores.ledger).map(Analysis(kb, ws, _))

  /** Writes the generated Lean; returns the files that changed. */
  def render: IO[List[String]] = analysis.flatMap(render)

  def render(a: Analysis): IO[List[String]] =
    val g = a.generate
    val keep = a.files.keySet.map(ws.lean.resolve(_).normalize)
    for
      _ <- Disk.update(ws.lean.resolve("lakefile.toml"), g.lakefile(ws.kernelPath))
      _ <- Disk.update(ws.lean.resolve("lean-toolchain"), "leanprover/lean4:v4.35.0\n")
      changed <- a.files.toList.sortBy(_._1).parTraverseN(8)((rel, text) => Disk.update(ws.lean.resolve(rel), text).map(Option.when(_)(rel)))
      stale <- g.layout.generatedDirs.map(ws.lean.resolve).flatTraverse(d => Disk.isDirectory(d).ifM(Disk.files(d), IO.pure(Nil)))
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
    yield Checked(results, a.withChecks(all))

  /** Where the knowledge base stands (see `Status`). */
  def status: IO[Status] = analysis.map(Status.of)

  def ci: IO[Ci] = check().map(c => Ci(c, Status.of(c.after)))

  /** Everything known about a node (see `Context`; `Context.text` is what `context` prints). */
  def context(n: Node[?]): IO[Context] =
    (analysis, stores.requests.load).parTupled.flatMap((a, rs) => codeDiff(a, n).map(Context.of(a, n, rs, _)))

  // How the code a node governs changed since it was decided: a git diff, or "".
  private def codeDiff(a: Analysis, n: Node[?]): IO[String] =
    val id = NodeId(n.id)
    if !a.annotated.byId.get(id).exists(_.review.causes.contains(Cause.Code)) then IO.pure("")
    else a.ledger.binding(id).zip(a.code(n)).fold(IO.pure("")) { (d, c) => codeSince(d, c.files) }

  /** How `files` changed since decision `d`: against the tree it recorded if this clone has it, else its commit. */
  def codeSince(d: Decision, files: List[String]): IO[String] =
    d.tree.filterA(stores.git.has).map(_.orElse(d.commit).getOrElse("")).flatMap(stores.git.diff(_, files))

  /** When a decision is taken, and the code as it is then (see `Stamp`). */
  def stamp(files: List[String]): IO[Stamp] =
    (IO.realTimeInstant, stores.git.head, stores.git.snapshot(files)).parMapN((at, head, tree) => Stamp(at.toString, head, tree))

  /** Creates or extends the proof file of a node with a stub for each open obligation; the file written. */
  def scaffold(n: Node[?]): IO[Option[String]] = analysis.flatMap(Scaffold(_, lake, n))

  /** Writes the snapshot to `.frflow/kb.json`. */
  def writeSnapshot(a: Analysis): IO[Path] =
    Disk.replace(ws.snapshotFile, Canonical.file(a.snapshot.asJson) + "\n").as(ws.snapshotFile)

  def writeSnapshot: IO[Path] = analysis.flatMap(writeSnapshot)

  /** Changes the ledger, under its lock, from the snapshot as it is now and the stamp of the code it
    * governs: the change `f` makes, or why it refuses.
    */
  def record[A](f: (Analysis, Stamp) => Ledger => Either[Refusal, (Ledger, A)]): IO[Either[Refusal, A]] =
    for
      a <- analysis
      st <- stamp(kb.nodes.flatMap(a.code).flatMap(_.files).distinct)
      out <- stores.ledger.update(f(a, st))
    yield out

  /** Applies a decision (see `Decide`), unsigned, and records it: for programs and tests. */
  def decide(r: DecisionRequest): IO[Either[Refusal, Unit]] =
    record((a, st) => l => Decide(a.snapshot, l, r, st).map(_ -> ()))

object Workflow:
  /** The files of the developer's decisions and requests, and git, in one workspace. */
  final case class Stores(ledger: LedgerStore, requests: RequestStore, git: Git)

  def apply(kb: KnowledgeBase, ws: Workspace): IO[Workflow] = Config.load.flatMap(apply(kb, ws, _))

  def apply(kb: KnowledgeBase, ws: Workspace, cfg: Config): IO[Workflow] =
    for
      lake <- Lake(ws.lean, cfg)
      ledger <- LedgerStore.make(ws.ledgerFile)
      requests <- RequestStore.make(ws.requestsFile)
    yield new Workflow(kb, ws, cfg, lake, Stores(ledger, requests, Git.at(ws.root)))
