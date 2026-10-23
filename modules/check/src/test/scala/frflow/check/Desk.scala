package frflow
package check

import cats.effect.IO
import cats.effect.unsafe.implicits.global
import cats.syntax.all.*
import frflow.ledger.*
import frflow.protocol.*
import java.nio.file.Path
import java.time.Instant

/** A knowledge base analysed over inputs held in memory: decisions change the ledger it holds, and nothing
  * is read or written but the files the nodes are written in (their definitions are part of what is decided).
  */
final case class Desk(kb: KnowledgeBase, inputs: Inputs):
  lazy val analysis: Analysis = Analysis(kb, Desk.ws, inputs)
  def annotated: Annotated = analysis.annotated
  def ledger: Ledger = inputs.ledger
  def state(n: Node[?]): ReviewState = annotated.byId.get(NodeId(n.id)).fold(ReviewState.Proposed)(_.state)
  def node(id: String): Reviewed = annotated.byId(NodeId(id))
  def causes(id: String): List[String] = node(id).review.causes.map(_.toString)
  def notAccepted: List[(String, String)] = kb.ordered.map(n => n.id -> state(n).toString).filter(_._2 != "accepted")

  /** The same decisions over another model, or another idea. */
  def withKb(other: KnowledgeBase): Desk = Desk(other, inputs.copy(texts = Desk.texts(other)))
  def withIdea(idea: String): Desk = copy(inputs = inputs.copy(idea = idea))

  /** Decided one second after the decision before (the review compares when decisions were taken). */
  def decide(d: Decide): Either[String, Desk] =
    val at = Instant.parse("2026-01-01T00:00:00Z").plusSeconds(ledger.all.size)
    Decide(analysis.snapshot, ledger, d, "dev", Stamp(at)).leftMap(_.message).map(l => copy(inputs = inputs.copy(ledger = l)))

  def accept(n: Node[?], reason: String): Either[String, Desk] = decide(Decide.Accept(List(NodeId(n.id)), reason))

  /** IDEA.md first, when there is one and it is not accepted: the root is decided after it. */
  def acceptAll: Desk =
    val idea = if annotated.idea.exists(_.state != ReviewState.Accepted) then Desk.ok(decide(Decide.Accept(List(IdeaDecision.Id), "it says what the system is for"))) else this
    kb.ordered.foldLeft(idea)((d, n) => Desk.ok(d.accept(n, s"${n.id} is right")))

object Desk:
  val idea = "# Shelf\n\nPick good items.\n\n## Not modelled\n\n- Prices.\n"
  val ws: Workspace = Workspace(Path.of("/nowhere"), "../lean")

  def apply(kb: KnowledgeBase): Desk = Desk(kb, Inputs.empty.copy(idea = idea, texts = texts(kb)))

  /** The files the nodes are written in (the test sources). */
  def texts(kb: KnowledgeBase): Map[String, String] = Inputs.texts(kb, ws).unsafeRunSync()

  def ok(e: Either[String, Desk]): Desk = e.fold(e => throw AssertionError(e), identity)

/** A knowledge base in a workspace on disk, read, decided and checked as the API does it (unsigned). */
final class OnDisk private (val kb: KnowledgeBase, val ws: Workspace, val cfg: Config, val lake: Lake, ledger: JsonStore[Ledger]):
  def analysis: IO[Analysis] = Analysis.read(kb, ws, cfg, ledger)
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
