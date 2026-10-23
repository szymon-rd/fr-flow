package frflow
package check

import cats.effect.unsafe.implicits.global
import cats.syntax.all.*
import frflow.ledger.*
import frflow.protocol.{NodeKind as _, *}
import java.nio.file.Path

/** A knowledge base analysed over inputs held in memory: decisions change the ledger it holds, and nothing
  * is read or written but the files the nodes are written in (their definitions are part of what is decided).
  */
final case class Desk(kb: KnowledgeBase, inputs: Inputs):
  lazy val analysis: Analysis = Analysis(kb, Desk.ws, inputs)
  def annotated: Annotated = analysis.annotated
  def ledger: Ledger = inputs.ledger
  def state(n: Node[?]): ReviewState = analysis.state(n)
  def node(id: String): Reviewed = annotated.byId(NodeId(id))
  def causes(id: String): List[String] = node(id).review.causes.map(_.toString)
  def notAccepted: List[(String, String)] = kb.ordered.map(n => n.id -> state(n).toString).filter(_._2 != "accepted")
  def allAccepted: Boolean = kb.nodes.forall(state(_) == ReviewState.Accepted)
  def context(n: Node[?]): String = Context.of(analysis, n, Nil, "").text
  def status: Status = Status.of(analysis)

  /** The same decisions over another model, or another idea. */
  def withKb(other: KnowledgeBase): Desk = Desk(other, inputs.copy(texts = Desk.texts(other)))
  def withIdea(idea: String): Desk = copy(inputs = inputs.copy(idea = idea))

  /** Decided one second after the decision before (the review compares when decisions were taken). */
  def decide(r: DecisionRequest): Either[String, Desk] =
    val at = java.time.Instant.parse("2026-01-01T00:00:00Z").plusSeconds(ledger.all.size)
    Decisions.decide(analysis.snapshot, ledger, r, at.toString).leftMap(_.message).map(l => copy(inputs = inputs.copy(ledger = l)))

  def accept(n: Node[?], reason: String, rejecting: List[Node[?]] = Nil, confirm: List[Node[?]] = Nil): Either[String, Desk] =
    decide(Desk.req(n.id, reason, reject = rejecting.map(_.id), confirm = confirm.map(_.id)))

  /** Every node accepted, in the order decisions are taken. */
  def acceptAll: Desk = accepting(kb.ordered*)
  def accepting(ns: Node[?]*): Desk = ns.foldLeft(this)((d, n) => Desk.ok(d.accept(n, s"${n.id} is right")))

object Desk:
  val idea = "# Shelf\n\nPick good items.\n\n## Not modelled\n\n- Prices.\n"
  val ws: Workspace = Workspace(Path.of("/nowhere"), "../lean")

  def apply(kb: KnowledgeBase): Desk = Desk(kb, Inputs.empty.copy(idea = idea, texts = texts(kb)))

  /** The files the nodes are written in (the test sources). */
  def texts(kb: KnowledgeBase): Map[String, String] = Inputs.texts(kb, ws).unsafeRunSync()

  def req(node: String, reason: String, reject: List[String] = Nil, revisit: List[String] = Nil, confirm: List[String] = Nil,
      action: Action = Action.Accept, seen: String = "", by: String = "dev"): DecisionRequest =
    def ids(xs: List[String]) = xs.map(NodeId(_))
    DecisionRequest(NodeId(node), by, reason, ids(reject), ids(revisit), ids(confirm), action, Option(seen).filter(_.nonEmpty))

  def ok(e: Either[String, Desk]): Desk = e.fold(e => throw AssertionError(e), identity)
