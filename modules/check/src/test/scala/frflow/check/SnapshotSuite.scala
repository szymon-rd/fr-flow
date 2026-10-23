package frflow
package check

import frflow.ledger.*
import frflow.fixtures.*
import frflow.protocol.{NodeKind as Kind, *}
import io.circe.Json
import io.circe.syntax.*
import Desk.ok
import java.time.Instant

/** The snapshot, the developer's decisions and how drift shows: in memory, without files or Lean. */
class SnapshotSuite extends munit.FunSuite:

  private def snapOf(s: Snapshot): Map[String, SnapNode] = s.nodes.map(n => n.id.value -> n).toMap
  private def ids(xs: String*): List[NodeId] = xs.map(NodeId(_)).toList
  private def words[A](xs: Seq[A]): List[String] = xs.map(_.toString).toList
  private def belowIds(d: Desk, id: String): List[String] = words(d.node(id).review.below.map(_.id))
  private def str(s: String): Json = Json.fromString(s)
  private def kbOf(ns: Seq[Node[?]]) = KnowledgeBase("Shelf", idea = "IDEA.md")(ns*)

  /** The shelf's parts and contract, built under a given root (a root reworded keeps them as they are). */
  private def under(root: Node[?], fromListStatement: String = fromList.statement): List[Node[?]] =
    val fl = Node.claim("FromList", fromListStatement, why = fromList.why)(
      forall((l: List[Book], n: Int) => picks(l, n).forall(b => l.contains(b)))).under(root)
    val ol = Node.claim("OnlyLong", onlyLong.statement, why = onlyLong.why)(
      forall((l: List[Book], n: Int) => picks(l, n).forall(b => b.pages >= minPages.value))).under(root)
    val c = Node.contract(picks)("Pick", "A call returns only long enough books of the shelf.", why = "Per call.")(
      (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages.value)).under(fl, ol)
      .examples(minPages.bind(100))(
        expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
        expect(List(Book("Short", 20)), 5, Nil, "none"),
        reject(List(Book("Short", 20)), 5, List(Book("Short", 20)), "a short book is never picked"))
    List(root, books, picking, fl, ol, c)
  // The root, reworded and its formula written otherwise: a change of what Lean reads.
  private def root2 = Node.claim("OnlyGood", "An item is picked from a list exactly when it is on the list and good, and only then.", onlyGood.why)(
    forall((l: List[Item.T], x: Item.T) => shown(l, x) == (good(x) && l.contains(x))))
  // The root reworded only: its formula as it was.
  private def rootReworded = Node.claim("OnlyGood", "An item is picked from a list exactly when it is on the list and good, and only then.", onlyGood.why)(
    forall((l: List[Item.T], x: Item.T) => shown(l, x) == (l.contains(x) && good(x))))
  private def alternative = Node.claim("Bounded", "Picked books come from the shelf, at most n of them.", why = "Readers want few books.")(
    forall((l: List[Book], n: Int) => picks(l, n).forall(b => l.contains(b)))).under(onlyGood).replaces(fromList)

  test("the snapshot is the DAG of the Scala definitions: parents, parts, definitions, the root") {
    val a = Desk(shelfKb).annotated
    val j = a.snapshot
    assertEquals(j.root, Some(NodeId("OnlyGood")))
    assertEquals(j.definitions, ids("Books", "Picking"))
    assertEquals(j.trusted, ids("Pick"))
    assertEquals(j.nodes.map(_.id), ids("Books", "Picking", "OnlyGood", "FromList", "OnlyLong", "EveryLong", "Pick"))
    val ns = snapOf(j)
    assertEquals(ns.view.mapValues(_.kind.toString).toMap,
      Map("OnlyGood" -> "claim", "Books" -> "definition", "Picking" -> "definition", "FromList" -> "claim", "OnlyLong" -> "claim", "EveryLong" -> "claim", "Pick" -> "contract"))
    assertEquals(ns("OnlyGood").parents, Nil)
    assertEquals(ns("OnlyGood").parts, ids("FromList", "OnlyLong", "EveryLong"))
    assertEquals(ns("Pick").parents, ids("FromList", "OnlyLong", "EveryLong"))
    assertEquals(ns("Pick").op, Some("picks"))
    assertEquals(ns("Books").defines, List("Item", "good"))
    assertEquals(ns("OnlyGood").uses.sorted, ids("Books", "Picking"))
    assertEquals(ns("OnlyGood").rule, false)
    assertEquals(ns("OnlyGood").leaf, false)
    assertEquals(ns("EveryLong").leaf, false)
    assertEquals(ns("OnlyGood").split.map(_.complete.status), Some(ObligationStatus.Unchecked))
    assertEquals(ns("OnlyGood").split.map(_.needed.map(_.id)), Some(ids("FromList", "OnlyLong", "EveryLong")))
    assertEquals(ns("Pick").split, None)
    assertEquals(a.byId(NodeId("FromList")).state, ReviewState.Proposed)
    assertEquals(ns("Pick").examples.map(_.codeFails), List.fill(4)(None))
    assertEquals(ns("Pick").examples.head.`given`, List("minPages = 100"))
    assertEquals(ns("Pick").code, None) // its implementation lives in the model's own file
    // the model's files are where its nodes are written; a model may span several
    assertEquals(shelfKb.modelFiles.map(f => java.nio.file.Paths.get(f).getFileName.toString), List("Fixtures.scala"))
    assertEquals((ns("Pick").examplesPassing, CodeProof.of(ns("Pick")), ns("Pick").parents), ((4, 4), Some(CodeProof.ByRunning), ids("FromList", "OnlyLong", "EveryLong")))
  }

  test("a claim with no parts is a leaf, trusted as it stands") {
    assert(snapOf(Desk(sloppyKb).analysis.snapshot)("Sloppy").leaf)
  }

  test("the DAG is decided from the root down; a part waits for all its parents and the definitions it uses") {
    val d = Desk(shelfKb)
    assert(d.accept(fromList, "because it is right").left.exists(_.contains("accept OnlyGood first")))
    assert(d.accept(onlyGood, "because it is right").left.exists(_.contains("accept Books first")))
    assert(d.accept(books, " ").left.exists(_.contains("reason")))
    val top = d.accepting(books, picking, onlyGood, fromList)
    assert(top.accept(pick, "Pick is right").left.exists(_.contains("accept OnlyLong first")))
    assert(top.accepting(onlyLong, everyLong, pick).allAccepted)
  }

  test("choosing one proposal rejects the alternatives it replaces; they are kept through later decisions") {
    val alt = alternative
    val d = ok(Desk(shelfWith(pick, alt)).accepting(books, picking, onlyGood).accept(fromList, "Books must come from the shelf."))
    assertEquals((d.state(fromList), d.state(alt)), (ReviewState.Accepted, ReviewState.Rejected))
    assertEquals(d.ledger.alternatives(NodeId("FromList")).map(_._1), ids("Bounded"))
    // the agent removes the rejected node, then rewords FromList; the new decision keeps the alternative
    val reworded = Node.claim("FromList", "Every picked book is on the shelf.", why = fromList.why)(
      forall((l: List[Book], n: Int) => picks(l, n).forall(b => l.contains(b)))).under(onlyGood)
    val d2 = d.withKb(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, books, picking, reworded))
    assertEquals(d2.state(reworded), ReviewState.Review)
    val d3 = ok(d2.accept(reworded, "The wording is clearer."))
    assertEquals(d3.node("FromList").review.decision.map(_.reason), Some("Books must come from the shelf."))
    assertEquals(d3.ledger.alternatives(NodeId("FromList")).map(_._1), ids("Bounded"))
    assertEquals(d3.ledger.history(NodeId("FromList")).map(_.action.toString), List("accept", "accept"))
  }

  test("a change to the idea's lead reviews the root only") {
    val d = Desk(shelfKb).acceptAll.withIdea("# Shelf\n\nPick good items, quickly.\n\n## Not modelled\n\n- Prices.\n")
    assertEquals(d.notAccepted, List("OnlyGood" -> "review"))
    assert(d.node("OnlyGood").node.content.str("idea").exists(_.contains("quickly")))
  }

  test("after a change, the developer names the decisions below that it may affect; a shared part is listed once") {
    val d = Desk(shelfKb).acceptAll.withIdea("# Shelf\n\nPick good items, quickly.\n\n## Not modelled\n\n- Prices.\n")
    assertEquals(belowIds(d, "OnlyGood").count(_ == "Pick"), 1)
    val d2 = ok(d.accept(onlyGood, "Picking must be quick now.", revisit = List(pick)))
    assert(d.accept(fromList, "OnlyGood is not below it.", revisit = List(onlyGood)).left.exists(_.contains("not among")))
    assertEquals(d2.notAccepted, List("Pick" -> "review"))
    assertEquals(d2.causes("Pick"), List("revisit"))
    val d3 = ok(d2.accept(pick, "Filtering a list is quick enough."))
    assertEquals(d3.ledger.history(NodeId("Pick")).map(_.action.toString), List("accept", "revisit", "confirm"))
    assertEquals(d3.node("Pick").review.decision.map(_.reason), Some("Pick is right"))
    assert(d3.node("Pick").review.history.exists(h => h.action == Action.Revisit && h.reason.startsWith("OnlyGood changed")))
  }

  test("a proposal can be rejected on its own; a reason takes a few words") {
    val alt = alternative
    val d = Desk(shelfWith(pick, alt))
    assert(d.accept(books, "ok").left.exists(_.contains("few words")))
    val d2 = ok(d.accepting(books, picking, onlyGood).reject("Bounded", "Readers want every good book."))
    assertEquals((d2.state(alt), d2.state(fromList)), (ReviewState.Rejected, ReviewState.Proposed))
    assert(d2.reject("OnlyGood", "The root is not a proposal.").left.exists(_.contains("only a proposal")))
  }

  test("rejecting a node puts what rests on it up for review, and status fails until it is moved") {
    val alt = alternative
    val d = ok(Desk(shelfWith(pick, alt)).accepting(shelfKb.ordered*).accept(alt, "Readers want fewer books now."))
    assertEquals(d.state(fromList), ReviewState.Rejected)
    assertEquals(d.causes("Pick"), List("above"))
    assert(d.accept(pick, "Pick still holds here.").left.exists(_.contains("accept FromList first")))
    assert(!d.complete)
    // The agent reads why: the reason may ask for something in the node's place.
    assertEquals(Waiting.forAgent(d.annotated), List(
      ForAgent.Replace(NodeId("FromList"), "dev", "Bounded was chosen instead: Readers want fewer books now."),
      ForAgent.Move(NodeId("Pick"), ids("FromList"))))
    assert(d.node("FromList").review.history.exists(h => h.action == Action.Reject && h.by == "dev"))
  }

  test("how the implementation is built is part of the contract's content") {
    assertEquals(shelfKb.implementation(pick).map(_.wiring), Some("(shelf, n) => shelf.filter(_.pages >= minPages.value)"))
    assertEquals(Desk(shelfKb).node("Pick").node.content.str("implementation"), Some("(shelf, n) => shelf.filter(_.pages >= minPages.value)"))
  }

  test("a decision is refused when the node moved since the developer looked at it") {
    val d = Desk(shelfKb)
    def seeing(v: String) = Decide.Accept(ids("Books"), "It is the idea.", seen = Map(NodeId("Books") -> v))
    assert(d.decide(seeing("stale")).left.exists(_.contains("changed since")))
    assert(d.decide(seeing(d.node("Books").review.version)).isRight)
  }

  test("when two branches decided the same node and both were kept, it is decided again") {
    val base = ok(Desk(shelfKb).accept(books, "it is the idea")).ledger
    val b = NodeId("Books")
    def d(r: String) = Decision(Action.Accept, "dev", Instant.EPOCH, r, content = base.history(b).head.content)
    val ours = base.add(b, d("on branch one"))
    val theirs = base.add(b, d("on branch two"))
    val merged = Ledger(Map(b -> (ours.history(b) :+ theirs.history(b).last)))
    assert(merged.forked(b))
    assert(!merged.add(b, d("decided again after the merge")).forked(b))
  }

  test("decisions below are confirmed with a change, only below nodes that are accepted") {
    val r2 = root2
    val now = under(r2, "Picked books come from the shelf, and nowhere else.")
    val d = Desk(kbOf(under(onlyGood))).acceptAll.withKb(kbOf(now))
    // FromList changed itself, so it is decided on its own; nothing below it is listed with the root
    assertEquals(belowIds(d, "OnlyGood"), List("OnlyLong"))
    assertEquals(ok(d.accept(r2, "Clearer with 'only then' added.")).notAccepted.map(_._1), List("FromList", "Pick"))
  }

  test("the definition as written runs past comments between its chained calls, and not into the next one's") {
    val d = Desk(shelfKb).analysis.definition(longPick)
    assert(d.startsWith("val longPick = ") && d.contains(".examples(") && d.endsWith("\"never a short one\"))"), d)
  }

  test("a change to a node's meaning shows below, and what still holds is confirmed by name") {
    val r2 = root2
    val now = under(r2)
    val d = Desk(kbOf(under(onlyGood))).acceptAll.withKb(kbOf(now))
    assertEquals(List("OnlyGood", "FromList", "Pick").map(d.causes), List(List("self"), List("above"), List("above")))
    assertEquals(d.node("OnlyGood").review.below.map(b => b.id.value -> b.kind.toString),
      List("FromList" -> "moved", "OnlyLong" -> "moved", "Pick" -> "moved")) // parents first
    val d2 = ok(d.accept(r2, "Clearer with 'only then' added."))
    assert(d2.allAccepted, d2.notAccepted)
    assertEquals(d2.ledger.history(NodeId("Pick")).map(_.action.toString), List("accept", "confirm"))
    assertEquals(d2.node("Pick").review.decision.map(_.reason), Some("Pick is right"))
  }

  test("a statement reworded, its formula unchanged, reviews that node only; what is below is listed under it, not sent to review") {
    val d = Desk(kbOf(under(onlyGood))).acceptAll.withKb(kbOf(under(rootReworded)))
    assertEquals(d.notAccepted, List("OnlyGood" -> "review"))
    assertEquals(d.causes("OnlyGood"), List("self"))
    // what may be affected: the decisions below it, each to revisit by name if it is
    assertEquals(d.node("OnlyGood").review.below.map(b => b.id.value -> b.kind.toString),
      List("FromList" -> "accepted", "OnlyLong" -> "accepted", "Pick" -> "accepted"))
    assertEquals(d.node("Pick").review.moved, Nil)
    val d2 = ok(d.accept(rootReworded, "Clearer with 'only then' added."))
    assert(d2.allAccepted, d2.notAccepted)
    // after it, a change of its formula still moves what is below
    assertEquals(d2.withKb(kbOf(under(root2))).causes("Pick"), List("above"))
  }

  test("what is not modelled can change without disturbing decisions") {
    val d = Desk(shelfKb).acceptAll.withIdea("# Shelf\n\nPick good items.\n\n## Not modelled\n\n- Prices.\n- Covers.\n")
    // only the root is reviewed: what is not modelled narrows nothing below it
    assertEquals(d.notAccepted, List("OnlyGood" -> "review"))
  }

  test("a decided node removed from the model shows until the removal is confirmed") {
    val d = Desk(shelfKb).acceptAll.withKb(kbOf(shelfNodes))
    assertEquals(d.annotated.gone.map(_.id), ids("Pick"))
    assert(!d.complete)
    assertEquals(ok(d.decide(Decide.Accept(ids("Pick"), "Picking moved to another service."))).annotated.gone, Nil)
  }

  test("the ledger is the history") {
    val d = ok(Desk(callsKb).accept(pickedAgain, "it is the idea"))
    assertEquals(d.ledger.all.map(_._1), ids("PickedAgain"))
    assertEquals(d.node("PickedAgain").review.decision.map(_.by), Some("dev"))
  }

  test("a change to what a term means reviews the nodes that use it") {
    val good2 = Param[Item.T => Boolean]("good", "whether an item is cheap")
    val onlyGood2 = Node.claim(onlyGood.id, onlyGood.statement, onlyGood.why)(
      forall((l: List[Item.T], x: Item.T) => shown(l, x) == (l.contains(x) && good2(x))))
    val d = Desk(shelfKb).acceptAll.withKb(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood2, books, picking))
    assertEquals(d.state(onlyGood2), ReviewState.Review)
  }

  private def thick = Node.definition("Books", "Items are books; a book is good when it is thick.", why = books.why)(
    Item := of[Book], good := ((b: Book) => b.pages >= 500))

  test("a change to a definition reviews the nodes that use its terms") {
    val d = Desk(shelfKb).acceptAll.withKb(kbOf((thick :: shelfNodes.filterNot(_ eq books)) :+ pick))
    assertEquals(d.causes("Books"), List("self"))
    assertEquals(d.causes("OnlyGood"), List("above"))
    // what does not use the term rests on what does: the root, whose meaning moved
    assertEquals(d.causes("FromList"), List("above"))
  }

  test("a definition with an alternative: what uses the term waits for the choice, and the choice is in force") {
    val other = Node.definition("Thick", "A book is good when it is thick.", why = "Readers want long reads.")(good := ((b: Book) => b.pages >= 500))
    val d = Desk(shelfWith(pick, other))
    assertEquals(d.analysis.generate.undecided, Set("good"))
    assertEquals(d.node("Thick").node.defines, List("good"))
    assert(Graph.alternatives(d.node("Thick").node, d.node("Books").node))
    val d2 = ok(d.accept(books, "Length is what readers asked for."))
    assertEquals(d2.state(other), ReviewState.Rejected)
    assertEquals(d2.analysis.generate.undecided, Set.empty[String])
    assertEquals(d2.analysis.generate.inForce.get("good").map(_.id), Some("Books"))
  }

  // Lean is not run here: these mark every node as Lean would.
  private def proven(s: Snapshot): Snapshot = s.copy(nodes = s.nodes.map(n => n.copy(
    status = n.status.map(_ => CheckStatus.Proven),
    split = n.split.map(_ => Split(Outcome(ObligationStatus.Proven, "auto"), Nil, Outcome(ObligationStatus.NotShown))))))
  /** The snapshot with one node's content changed (and its hash with it). */
  private def changing(s: Snapshot, id: String)(f: PartialFunction[(String, Json), (String, Json)]): Snapshot =
    s.copy(nodes = s.nodes.map(n => if n.id != NodeId(id) then n else
      val c = n.content.mapFields(f)
      n.copy(content = c, hash = c.hash)))
  private def decideOn(s: Snapshot, l: Ledger, id: String, action: Action, i: Int) =
    val d = if action == Action.Reject then Decide.Reject(NodeId(id), s"$id holds for this reason") else Decide.Accept(ids(id), s"$id holds for this reason")
    Decide(s, l, d, "dev", Stamp(Instant.parse(f"2026-01-01T00:00:$i%02dZ"))).left.map(_.message)
  private def decided(s: Snapshot, l: Ledger, ids: List[String], from: Int) =
    ids.zipWithIndex.foldLeft(l)((l, x) => decideOn(s, l, x._1, Action.Accept, from + x._2).fold(e => fail(e), identity))

  test("a decision is mechanical only where Lean proves it again and nothing in it is a choice; the agent decides nothing") {
    val snap = proven(Desk(shelfKb).analysis.snapshot)
    val ns = snapOf(snap)
    val l1 = decided(snap, Ledger.empty, List("Books", "Picking", "OnlyGood"), 1)
    assert(Reading(snap, l1).mechanical(ns("Books")).exists(_.contains("definition nodes hold a choice")))
    // a proposal is the developer's choice
    assert(Reading(snap, l1).mechanical(ns("FromList")).exists(_.contains("only a node under review")))
  }

  test("deciding a large tree stays fast: each node's state is computed once") {
    // 800 nodes, eight children per node, all accepted
    val ns = (0 until 800).toList.map { i =>
      val c = Content("statement" -> str(s"node $i"))
      SnapNode(NodeId(s"N$i"), Kind.Claim, c, c.hash, parents = if i == 0 then Nil else ids(s"N${(i - 1) / 8}"))
    }
    val snap = Snapshot("Large", ns)
    val ledger = ns.foldLeft(Ledger.empty)((l, n) => l.add(n.id, Decision(Action.Accept, "dev", Instant.EPOCH, "it is right",
      chain = Graph(snap).parentChainAlone(n), content = n.content)))
    val t = System.nanoTime
    val a = Annotate(snap, ledger)
    val seconds = (System.nanoTime - t) / 1e9
    assert(a.nodes.forall(_.state == ReviewState.Accepted), a.nodes.head)
    assert(seconds < 5, s"$seconds s")
  }

  test("rejecting a proposal rejects what rests on it; a reworded why is the theory, not mechanical, and does not cascade") {
    val snap = proven(Desk(shelfKb).analysis.snapshot)
    val l1 = decided(snap, Ledger.empty, List("Books", "Picking", "OnlyGood"), 1)
    val rejected = decideOn(snap, l1, "FromList", Action.Reject, 5).fold(e => fail(e), identity)
    assertEquals(ids("FromList", "Pick").map(rejected.current(_).map(_.action)), List.fill(2)(Some(Action.Reject)))
    // all accepted; then only FromList's why is reworded
    val all = decided(snap, l1, List("FromList", "OnlyLong", "EveryLong", "Pick"), 10)
    val reworded = changing(snap, "FromList") { case ("why", _) => "why" -> str("Reworded, saying the same.") }
    val rs = snapOf(reworded)
    assertEquals(Reading(reworded, all).causes(rs("FromList")), List(Cause.Self))
    assert(Reading(reworded, all).mechanical(rs("FromList")).isDefined)
    assert(Reading(reworded, all).causes(rs("Pick")).isEmpty) // a why does not cascade
  }

  test("a node whose code calls another contract's operation rests on that contract") {
    val promise2 = Node.contract(picks)("PickPromise", "A call returns only long enough books, from the shelf.", why = pickPromise.why)(
      (shelf, n, picked) => picked.forall(b => b.pages >= minPages.value && shelf.contains(b)))
      .examples(minPages.bind(100))(
        expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
        reject(List(Book("Short", 20)), 5, List(Book("Short", 20)), "never a short one"))
    val kb = KnowledgeBase("Calls", idea = "IDEA.md")(pickedAgain, againC, promise2).implementProven(promise2)(longOnes).implementProven(againC)(viaPick)
    val d = Desk(callsKb).acceptAll.withKb(kb)
    assertEquals(d.analysis.restsOn(againC).map(_.id), List("PickedAgain", "PickPromise"))
    assertEquals(d.causes("Again"), List("above"))
    assertEquals(d.node("Again").node.relies, ids("PickPromise"))
    assertEquals(d.annotated.nodes.filter(_.node.relies.contains(NodeId(promise2.id))).map(_.id), ids("Again"))
  }

  test("any node may name a section of the idea; a section no node names is a warning") {
    val long2 = Node.claim("OnlyLong", onlyLong.statement, onlyLong.why, idea = "Picking")(
      forall((l: List[Book], n: Int) => picks(l, n).forall(b => b.pages >= minPages.value))).under(onlyGood)
    val d = Desk(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, books, picking, long2))
      .withIdea("# Shelf\n\nPick good items.\n\n## Picking\n\nPick only long books.\n\n## Selling\n\nSell them.\n\n## Not modelled\n\n- Prices.\n")
    assert(d.node("OnlyLong").node.content.str("notModelled").exists(_.contains("Prices")))
    assert(d.node("OnlyLong").node.content.str("idea").exists(_.contains("Pick only long books")))
    assert(d.node("OnlyGood").node.content.str("idea").exists(i => i.contains("Pick good items") && !i.contains("long books")))
    val warnings = Governance.codeWarnings(d.analysis)
    assert(warnings.exists(_.contains("the section \"Selling\"")), warnings)
    assert(!warnings.exists(_.contains("the section \"Picking\"")), warnings)
  }

  test("a revisit it cannot apply is refused, with why, not dropped") {
    val d = Desk(kbOf(under(onlyGood))).acceptAll.withKb(kbOf(under(root2)))
    val h = d.decide(Decide.Accept(ids("OnlyGood"), "Clearer with only then added.", ids("Elsewhere")))
    assert(h.left.exists(_.contains("not among")), h)
    assert(d.decide(Decide.Accept(ids("OnlyGood"), "Clearer with 'only then' added.", ids("FromList"))).isRight)
  }

  test("a type change is mechanical where nothing the developer decided changed") {
    val d = Desk(shelfKb).acceptAll
    val snap = proven(d.analysis.snapshot)
    def withUses(f: Vector[Json] => Vector[Json]) =
      changing(snap, "Pick") { case ("uses", u) => "uses" -> Json.fromValues(f(u.asArray.getOrElse(Vector.empty))) }
    // Book gains a field: only the types Pick uses changed, and how its examples print
    val changed = withUses(_.map(u => if u.asString.exists(_.startsWith("case class Book")) then str("case class Book(title: String, pages: Int, author: String)") else u))
    val pickNode = snapOf(changed)("Pick")
    assertEquals(Reading(changed, d.ledger).state(pickNode), ReviewState.Review)
    assertEquals(Reading(changed, d.ledger).mechanical(pickNode), None)
    // a definition it calls is part of what it says: not mechanical
    val redefined = withUses(_ :+ str("long = (b: Book) => b.pages >= 10"))
    assert(Reading(redefined, d.ledger).mechanical(snapOf(redefined)("Pick")).exists(_.contains("changed")))
  }

  test("alternatives are a node and the one it replaces, or two definitions of one term; parts of one parent are not") {
    def n(id: String, kind: Kind = Kind.Claim, replaces: Option[String] = None, defines: List[String] = Nil) =
      SnapNode(NodeId(id), kind, Content.empty, Content.empty.hash, parents = if kind == Kind.Definition then Nil else ids("R"),
        replaces = replaces.map(NodeId(_)), defines = defines)
    val (a, b, c) = (n("A"), n("B", replaces = Some("A")), n("C"))
    val (d1, d2) = (n("D1", Kind.Definition, defines = List("good")), n("D2", Kind.Definition, defines = List("good", "Item")))
    assert(Graph.alternatives(a, b) && Graph.alternatives(b, a) && Graph.alternatives(d1, d2))
    assert(!Graph.alternatives(a, c) && !Graph.alternatives(a, d1))
  }

  /** The shelf's nodes and more, with Pick implemented as in `shelfKb`. */
  private def shelfAnd(ns: Node[?]*) = kbOf(shelfNodes ++ ns).implement(pick)((shelf, n) => shelf.filter(_.pages >= minPages.value))

  /** A diamond: D is a part of B and of C, both parts of A. Without `dUnderC`, D is a part of B only. */
  private def diamond(top: String = "Results are never negative.", dUnderC: Boolean = true): List[Node[?]] =
    // Reworded, the top says it in Lean otherwise too: a change of meaning.
    val a = if top == "Results are never negative." then Node.claim("A", top, why = "The purpose.")(forall((x: BigInt) => sq(x) >= 0))
      else Node.claim("A", top, why = "The purpose.")(forall((x: BigInt) => sq(x) > -1))
    val b = Node.claim("B", "Results are at least zero.", why = "Zero is the floor.")(forall((x: BigInt) => sq(x) >= 0)).under(a)
    val c = Node.claim("C", "Results are zero or more.", why = "Said otherwise.")(forall((x: BigInt) => sq(x) >= 0)).under(a)
    val d = if dUnderC then squaresOf(b, c) else squaresOf(b)
    List(a, b, c, d)
  private def squaresOf(ps: Node[?]*) =
    Node.claim("D", "The result is the square of the input.", why = "Squares are never negative.")(forall((x: BigInt) => sq(x) == x * x)).under(ps*)
  private val newPart = Node.claim("Bounded", "At most n books are picked.", why = "Readers want few books.")(
    forall((l: List[Book], n: Int) => picks(l, n).length <= n)).under(fromList)

  test("a part added puts its parent up for review, with the cause `parts`, and nothing else; the new part waits for it") {
    val d = Desk(shelfKb).acceptAll.withKb(shelfAnd(pick, newPart))
    assertEquals(d.causes("FromList"), List("parts"))
    assertEquals(d.notAccepted, List("FromList" -> "review", "Bounded" -> "proposed"))
    assertEquals(d.node("Bounded").review.waitsFor.map(_.value), Some("FromList"))
    // these parts make it: a confirmation, which keeps the reason it was chosen and binds the parts
    val d2 = ok(d.accept(fromList, "FromList is still made by its parts."))
    assertEquals(d2.ledger.history(NodeId("FromList")).map(_.action.toString), List("accept", "confirm"))
    assertEquals(d2.node("FromList").review.decision.map(_.reason), Some("FromList is right"))
    assertEquals(d2.ledger.binding(NodeId("FromList")).map(_.content.strs("parts")), Some(List("Pick", "Bounded")))
    val d3 = ok(d2.accept(newPart, "A bound helps readers."))
    assert(d3.allAccepted, d3.notAccepted)
    // and removed: the parent again
    val back = d3.withKb(shelfKb)
    assertEquals(back.notAccepted, List("FromList" -> "review"))
    assertEquals(back.causes("FromList"), List("parts"))
    assertEquals(back.annotated.gone.map(_.id), ids("Bounded"))
  }

  test("a change of parts is mechanical when Lean proves the parts make it, each needed; not otherwise") {
    val d = Desk(shelfKb).acceptAll.withKb(shelfAnd(pick, newPart))
    val snap = proven(d.analysis.snapshot)
    val ns = snapOf(snap)
    def mechanical(s: Snapshot, n: SnapNode) = Reading(s, d.ledger).mechanical(n)
    assertEquals(Reading(snap, d.ledger).causes(ns("FromList")), List(Cause.Parts))
    assertEquals(mechanical(snap, ns("FromList")), None)
    import ObligationStatus.{NotShown as Needed, Shown as NotNeeded, Open, Proven}
    def withSplit(complete: ObligationStatus, needed: ObligationStatus) = snap.copy(nodes = snap.nodes.map(n => if n.id != NodeId("FromList") then n
      else n.copy(split = Some(Split(Outcome(complete), ids("Pick", "Bounded").map(Split.Part(_, needed, "")), Outcome(ObligationStatus.NotShown))))))
    def fromList(s: Snapshot) = snapOf(s)("FromList")
    assertEquals(mechanical(withSplit(Proven, Needed), ns("FromList")), None)
    // a part not needed (Lean shows the parent without it), or the parts not shown to make it: the developer decides
    assert(mechanical(withSplit(Proven, NotNeeded), fromList(withSplit(Proven, NotNeeded))).isDefined)
    assert(mechanical(withSplit(Open, Needed), fromList(withSplit(Open, Needed))).isDefined)
    // a proposal is never mechanical
    assert(mechanical(snap, ns("Bounded")).exists(_.contains("proposed")))
  }

  test("a diamond: the node under two parents is reviewed once, listed once after both, and confirmed once") {
    val now = diamond("Results are never negative, whatever the input.")
    val d = Desk(kbOf(diamond())).acceptAll.withKb(kbOf(now))
    assertEquals(List("A", "B", "C", "D").map(d.causes), List(List("self"), List("above"), List("above"), List("above")))
    assertEquals(belowIds(d, "A"), List("B", "C", "D"))
    // D waits for its parents, which wait for A
    assert(d.accept(now(3), "D still holds.").left.exists(_.contains("accept B first")))
    assert(d.accept(now(2), "C still holds.").left.exists(_.contains("accept A first")))
    val d2 = ok(d.accept(now(0), "Clearer about every input."))
    assert(d2.allAccepted, d2.notAccepted)
    assertEquals(d2.ledger.history(NodeId("D")).map(_.action.toString), List("accept", "confirm"))
  }

  test("a proposal waits for all of its parents") {
    def accept(d: Desk, id: String) = d.decide(Decide.Accept(ids(id), s"$id is right"))
    val d = List("A", "B").foldLeft(Desk(kbOf(diamond())))((d, id) => ok(accept(d, id)))
    assertEquals(d.node("D").review.waitsFor.map(_.value), Some("C"))
    assert(accept(d, "D").left.exists(_.contains("accept C first")))
    assert(accept(ok(accept(d, "C")), "D").isRight)
  }

  test("a node placed under a second parent: that parent reviews its parts; the node rests on more, and says the same") {
    val d = Desk(kbOf(diamond(dUnderC = false))).acceptAll.withKb(kbOf(diamond()))
    assertEquals(List("A", "B", "C", "D").map(d.causes), List(Nil, Nil, List("parts"), List("above")))
    val snap = proven(d.analysis.snapshot)
    // both mechanical: Lean proves C's parts make it, and D says what it said
    assertEquals(List("C", "D").map(id => Reading(snap, d.ledger).mechanical(snapOf(snap)(id))), List(None, None))
  }

  test("a change to a definition lists what rests on it, however far down, each once, to confirm by name") {
    val now = (thick :: shelfNodes.filterNot(_ eq books)) :+ pick
    val d = Desk(shelfKb).acceptAll.withKb(kbOf(now).implement(pick)((shelf, n) => shelf.filter(_.pages >= minPages.value)))
    val below = Set("OnlyGood", "FromList", "OnlyLong", "EveryLong", "Pick")
    assertEquals(belowIds(d, "Books"), List("OnlyGood", "FromList", "OnlyLong", "EveryLong", "Pick"))
    assert(ok(d.accept(now.head, "Readers want thick books now.")).allAccepted)
  }

  test("the alternatives of each node in the model: what it replaces or is replaced by, other definitions of its terms; never its siblings") {
    val other = Node.definition("Thick", "A book is good when it is thick.", why = "Readers want long reads.")(good := ((b: Book) => b.pages >= 500))
    val d = Desk(shelfWith(pick, alternative, other))
    def rivals(id: String) = words(d.node(id).review.rivals)
    assertEquals(List("FromList", "Bounded", "Books", "Thick", "OnlyLong").map(rivals), List(List("Bounded"), List("FromList"), List("Thick"), List("Books"), Nil))
  }

  test("placing a node under another parent changes where it rests, not what it says") {
    def node(parents: List[String], under: String) =
      val c = Content("kind" -> str("claim"), "parents" -> Json.fromValues(parents.map(str)), "parts" -> Json.arr(), "statement" -> str("The result is a square."),
        "definition" -> str(s"val d = Node.claim(\"D\", \"The result is a square.\", why = \"w\")(f)\n  .under($under)\n  .examples()()"))
      SnapNode(NodeId("D"), Kind.Claim, c, c.hash, parents = ids(parents*))
    val before = node(List("B"), "b")
    val ledger = Ledger.empty.add(NodeId("D"), Decision(Action.Accept, "dev", Instant.EPOCH, "it is right", content = before.content))
    val now = node(List("B", "C"), "b, c")
    assertEquals(Reading(Snapshot("S", List(now)), ledger).causes(now), Nil)
    // what it says, changed beside the call that places it: itself
    val c = now.content.mapFields { case ("definition", d) => "definition" -> str(d.asString.getOrElse("").replace(".examples()()", ".examples()(expect(1))")) }
    val reworded = now.copy(content = c, hash = c.hash)
    assertEquals(Reading(Snapshot("S", List(reworded)), ledger).causes(reworded), List(Cause.Self))
  }
