package frflow.decision

import frflow.core.name.NodeId
import frflow.core.spec.NodeKind
import frflow.decision.content.{CodeFingerprint, CodeNow, Content, FieldValue}
import frflow.decision.ledger.{Action, Authorship, Decision, Ledger, Reason}
import frflow.decision.review.{Place, ProofStanding, Reading, Subject, Subjects, Unproven}
import frflow.decision.rules.{Command, Decide, Refusal}
import java.time.Instant

/** Subjects written by hand, for the decision tests: a root `R`, its part `A`, and `A`'s part `B`, each with its
  * statement and its formula.
  */
object Shelf:
  def id(s: String): NodeId = NodeId(s)
  def ids(xs: String*): List[NodeId] = xs.map(NodeId(_)).toList
  def text(s: String): FieldValue = FieldValue.Text(s)
  def texts(xs: String*): FieldValue = FieldValue.Texts(xs.toList)

  /** Proven again but for `open`; no parts proven to make it, no code proven. */
  def unproven(open: List[Unproven]): ProofStanding = ProofStanding(open, false, false)

  def node(name: String, statement: String, parents: List[String], parts: List[String]): Subject =
    val content = Content(List("kind" -> text("claim"), "parents" -> texts(parents*), "parts" -> texts(parts*),
      "statement" -> text(statement), "formula" -> text(s"holds $name"),
      "vocabulary" -> texts(s"$name: what it is about")))
    val place = Place(ids(parents*), ids(parents*), Nil, NodeKind.Claim)
    Subject(id(name), content, place, None, unproven(Nil))

  extension (s: Subject)
    /** Its field `name` set to `v`, kept in its place, or added last. */
    def said(name: String, v: FieldValue): Subject =
      val fields = s.content.fields
      val set = if fields.exists(_._1 == name) then fields.map((k, x) => k -> (if k == name then v else x))
        else fields :+ (name -> v)
      s.copy(content = Content(set))
    def restated(statement: String): Subject = said("statement", text(statement))
    /** Its formula changed, and its words. */
    def remeant(statement: String): Subject = restated(statement).said("formula", text(s"changed ${s.id.value}"))
    def resting(on: String*): Subject = s.copy(place = s.place.copy(restsOn = s.place.restsOn ++ ids(on*)))
    def rivalling(others: String*): Subject = s.copy(place = s.place.copy(rivals = ids(others*)))
    def kind(k: NodeKind): Subject = said("kind", text(k.toString.toLowerCase)).copy(place = s.place.copy(kind = k))
    def coded(fingerprint: String): Subject =
      s.copy(code = Some(CodeNow(List("Shelf.scala"), CodeFingerprint(fingerprint))))

  val r: Subject = node("R", "Readers find the books they ask for.", Nil, List("A"))
  val a: Subject = node("A", "Every book asked for is on a shelf.", List("R"), List("B"))
  val b: Subject = node("B", "Each shelf lists its books.", List("A"), Nil)
  val shelf: Subjects = Subjects(List(r, a, b))

  def replacing(s: Subjects, n: Subject): Subjects = Subjects(s.inOrder.map(m => if m.id == n.id then n else m))

  def at(i: Int): Instant = Instant.parse(f"2026-01-01T00:00:$i%02dZ")
  def by(i: Int): Authorship = Authorship("dev", at(i), None)

  /** Accepting `node`, for a reason of its own unless one is given. */
  def accept(node: String, reason: String = "", revisit: List[String] = Nil, seen: Option[String] = None): Command =
    Command.Accept(ids(node), if reason.isEmpty then s"$node holds for this reason" else reason, ids(revisit*),
      seen.map(id(node) -> _).toMap)

  def right[A](e: Either[Refusal, A]): A = e.fold(r => throw AssertionError(r.toString), identity)

  /** Every node accepted, one decision each, in order. */
  def acceptAll(s: Subjects, from: Ledger = Ledger.empty): Ledger =
    s.inOrder.zipWithIndex.foldLeft(from)((l, x) => right(Decide(Reading(s, l), accept(x._1.id.value), by(1 + x._2))))

  /** `l` with R accepted as it is in `s`, and nothing else decided again. */
  def onlyRoot(s: Subjects, l: Ledger): Ledger =
    val root = s.get(id("R")).getOrElse(r)
    val reason = Reason("R holds for this reason", Nil)
    l.add(root.id, Decision.taken(Action.Accept, by(30), reason, Reading(s, l).bound(root)))
