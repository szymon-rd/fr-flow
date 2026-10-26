package frflow.api

import frflow.ledger.{Annotate, Decide, Graph, Stamp}
import frflow.protocol.*
import io.circe.Json
import java.time.Instant

/** A small knowledge base as a snapshot, decided by hand: a root with two claims sharing a contract, a
  * definition, an assumption under no parent, and a design node; then the contract reworded (under
  * review), a new proposal, a rejected one, and requests. It reads no files and runs no Lean.
  */
object Sample:
  val by = "dev"
  val at = Instant.parse("2026-01-02T10:00:00Z")

  private def str(s: String) = Json.fromString(s)
  private def strs(xs: String*) = Json.fromValues(xs.map(Json.fromString))

  private def content(kind: NodeKind, parents: List[String], parts: Option[List[String]], statement: String, why: String,
      sources: List[(String, String)] = Nil, vocabulary: List[String] = Nil) =
    Content((List("kind" -> str(kind.toString), "parents" -> strs(parents*)) ++ parts.map(p => "parts" -> strs(p*)) ++ List(
      "statement" -> str(statement), "why" -> str(why),
      "sources" -> Json.obj(sources.map((k, v) => k -> str(v))*), "vocabulary" -> strs(vocabulary*)))*)

  private def proven(id: String, parts: List[String]) =
    Some(Split(Outcome(ObligationStatus.Proven, "auto"), parts.map(p => Split.Part(NodeId(p), ObligationStatus.NotShown,
      s"Lean found no proof that $id holds without it (a try)")), Outcome(ObligationStatus.NotShown, "Lean found no proof that the parts contradict each other (a try)")))

  private def node(id: String, kind: NodeKind, parents: List[String], parts: List[String], statement: String, why: String,
      sources: List[(String, String)] = Nil, uses: List[String] = Nil, status: Option[CheckStatus] = Some(CheckStatus.Proven),
      examples: List[ExampleView] = Nil, code: Option[CodeRef] = None, op: Option[String] = None,
      vocabulary: List[String] = Nil, defines: List[String] = Nil, replaces: Option[String] = None): SnapNode =
    val statementLike = kind == NodeKind.Claim || kind == NodeKind.Contract || kind == NodeKind.Assumption
    val c = content(kind, parents, Option.when(statementLike)(parts), statement, why, sources, vocabulary)
    SnapNode(NodeId(id), kind, c, c.hash, parents.map(NodeId(_)), parts.map(NodeId(_)), replaces = replaces.map(NodeId(_)), op = op,
      defines = defines, uses = uses.map(NodeId(_)), status = status, examples = examples, code = code,
      // A contract's design nodes are not parts Lean reads: it has no split.
      split = Option.when(statementLike && parts.nonEmpty && kind != NodeKind.Contract)(proven(id, parts)).flatten)

  private def example(note: String, call: String, ok: Boolean = true) =
    ExampleView(note, List("grants = List(Grant(alice, /a))"), call, expected = true, Option.when(!ok)("returned None"),
      None, Some(Outcome(ObligationStatus.Proven, "Lean agrees")), None)

  val definition = node("Identities", NodeKind.Definition, Nil, Nil, "Users are named by ids, and resources are paths.",
    "Ids are what the session table stores.", status = None, defines = List("User"))
  val decide = node("Decide", NodeKind.Contract, List("NeedsGrant", "LetsIn"), List("Memory"),
    "A request is admitted on behalf of its token's user exactly when a grant names that user and the path.",
    "One call meets both rules at once.", List("post" -> "(t, p, d) => d == sessions(t).filter(u => grants(u, p))"),
    op = Some("admit"), examples = List(example("Alice's token and a grant: she gets in", "admit(t1, /a) == Some(alice)"),
      example("no grant for /b: refused", "admit(t1, /b) == None")),
    code = Some(CodeRef(List("src/main/scala/auth/Store.scala"), Fingerprint("f1"))),
    vocabulary = List("admit: the system's decision on a request", "grants: the grant table"))
  val memory = node("Memory", NodeKind.Design, List("Decide"), Nil, "Sessions and grants are kept in memory.", "One process decides.",
    status = None, code = Some(CodeRef(List("src/main/scala/auth/Server.scala"), Fingerprint("f2"))))
  val needsGrant = node("NeedsGrant", NodeKind.Claim, List("Root"), List("Decide"), "A request is admitted only with a grant for the path.",
    "Access needs a grant.", List("formula" -> "forall((t, p) => admit(t, p).forall(u => grants(u, p)))"), uses = List("Identities"))
  val letsIn = node("LetsIn", NodeKind.Claim, List("Root"), List("Decide"), "A request with a grant for the path is admitted.",
    "A grant is enough.", List("formula" -> "forall((t, p) => sessions(t).forall(u => grants(u, p) ==> admit(t, p) == Some(u)))"))
  val root = node("Root", NodeKind.Claim, Nil, List("NeedsGrant", "LetsIn"),
    "A user gets access to a resource exactly when they are signed in and authorized for it.", "The purpose of the system.",
    List("formula" -> "forall((u, r) => access(u, r) == (signedIn(u) && authorized(u, r)))"))
  val store = node("StoreKeeps", NodeKind.Assumption, Nil, Nil, "The store returns what was last written.", "The database's promise.")

  val decided: Snapshot = Snapshot("Sample", List(root, needsGrant, letsIn, decide, memory, definition, store),
    root = Some(NodeId("Root")), definitions = List(NodeId("Identities")), trusted = List(NodeId("StoreKeeps")))

  private def accept(s: Snapshot, l: Ledger, id: String, reason: String): Ledger =
    Decide(s, l, Decide.Accept(List(NodeId(id)), reason), by, Stamp(at)).fold(e => sys.error(s"$id: ${e.message}"), identity)

  /** Every node accepted, in the order decisions are taken. */
  val ledger: Ledger = Graph(decided).order.foldLeft(Ledger.empty)((l, id) => accept(decided, l, id.value, s"${id.value} holds as stated"))

  /** Then: the contract reworded (under review, with what it rests on), a new proposal under the root,
    * and one rejected beside it.
    */
  val reworded = decide.copy(content = content(NodeKind.Contract, List("NeedsGrant", "LetsIn"), Some(List("Memory")),
    "A request is admitted on behalf of the user its token was issued to, exactly when a grant names them and the path.",
    "One call meets both rules at once.", List("post" -> "(t, p, d) => d == sessions(t).filter(u => grants(u, p))"),
    List("admit: the system's decision on a request", "grants: the grant table")))
  val expiry = node("Expiry", NodeKind.Claim, List("Root"), Nil, "A session ends an hour after sign-in.", "Stolen tokens expire.",
    List("formula" -> "forall((t: Token, now: Instant) => sessions(t, now).isDefined == (issued(t).exists(at => now.isBefore(at.plus(hour)))))"),
    status = Some(CheckStatus.Open))
  val forever = node("Forever", NodeKind.Claim, List("Root"), Nil, "A session never ends.", "Simplest.", status = Some(CheckStatus.Open))

  val grown = node("Root", NodeKind.Claim, Nil, List("NeedsGrant", "LetsIn", "Expiry", "Forever"),
    "A user gets access to a resource exactly when they are signed in and authorized for it.", "The purpose of the system.",
    List("formula" -> "forall((u, r) => access(u, r) == (signedIn(u) && authorized(u, r)))"))

  val snapshot: Snapshot =
    val changed = Map(decide.id -> reworded.copy(hash = reworded.content.hash), root.id -> grown)
    decided.copy(nodes = decided.nodes.map(n => changed.getOrElse(n.id, n)) ++ List(expiry, forever))

  val ledgerNow: Ledger = Decide(snapshot, ledger, Decide.Reject(NodeId("Forever"), "sessions must end: a stolen token would work forever"), by,
    Stamp(Instant.parse("2026-01-03T09:00:00Z"))).fold(e => sys.error(e.message), identity)

  def view(s: Snapshot = snapshot, l: Ledger = ledgerNow): View = View(Annotate(s, l), Nil, Nil)
