package frflow
package check

import frflow.ledger.*
import frflow.fixtures.*
import frflow.protocol.{NodeKind as Kind, *}
import io.circe.Json
import Desk.ok
import java.time.Instant

/** How the Scala definitions become the snapshot the developer decides, and how their changes show: in memory, without Lean. */
class SnapshotSuite extends munit.FunSuite:

  private def snapOf(s: Snapshot): Map[String, SnapNode] = s.nodes.map(n => n.id.value -> n).toMap
  private def ids(xs: String*): List[NodeId] = xs.map(NodeId(_)).toList
  private def str(s: String): Json = Json.fromString(s)
  private def kbOf(ns: Seq[Node[?]]) = KnowledgeBase("Shelf", idea = "IDEA.md")(ns*)

  test("the snapshot is the DAG of the Scala definitions: parents, parts, definitions, the root") {
    val a = Desk(shelfKb).annotated
    val j = a.snapshot
    assertEquals(j.root, Some(NodeId("OnlyGood")))
    assertEquals(j.definitions, ids("Books", "Picking"))
    assertEquals(j.trusted, ids("Pick"))
    assertEquals(j.nodes.map(_.id), ids("Books", "Picking", "OnlyGood", "FromList", "OnlyLong", "EveryLong", "Pick"))
    val ns = snapOf(j)
    assertEquals((ns("OnlyGood").parents, ns("OnlyGood").parts, ns("OnlyGood").uses.sorted), (Nil, ids("FromList", "OnlyLong", "EveryLong"), ids("Books", "Picking")))
    assertEquals((ns("Pick").op, ns("Books").defines), (Some("picks"), List("Item", "good")))
    // a claim with no parts is a leaf, trusted as it stands
    assert(snapOf(Desk(sloppyKb).analysis.snapshot)("Sloppy").leaf)
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

  test("the content holds how the implementation is built, and the definition as written, past comments between its calls") {
    assertEquals(shelfKb.implementation(pick).map(_.wiring), Some("(shelf, n) => shelf.filter(_.pages >= minPages.value)"))
    assertEquals(Desk(shelfKb).node("Pick").node.content.str("implementation"), Some("(shelf, n) => shelf.filter(_.pages >= minPages.value)"))
    val d = Desk(shelfKb).analysis.definition(longPick)
    assert(d.startsWith("val longPick = ") && d.contains(".examples(") && d.endsWith("\"never a short one\"))"), d)
  }

  test("a change to the idea's lead, or to what is not modelled, reviews the root only") {
    val ideas = List("# Shelf\n\nPick good items, quickly.\n\n## Not modelled\n\n- Prices.\n", "# Shelf\n\nPick good items.\n\n## Not modelled\n\n- Prices.\n- Covers.\n")
    for idea <- ideas do assertEquals(Desk(shelfKb).acceptAll.withIdea(idea).notAccepted, List("OnlyGood" -> "review"), idea)
    assert(Desk(shelfKb).withIdea(ideas.head).node("OnlyGood").node.content.str("idea").exists(_.contains("quickly")))
  }

  private def thick = Node.definition("Books", "Items are books; a book is good when it is thick.", why = books.why)(
    Item := of[Book], good := ((b: Term[Book]) => b.pages >= 500))

  test("a change to what a term means, or to a definition, reviews the nodes that use it, and what rests on them") {
    val good2 = Param[Item.T => Boolean]("good", "whether an item is cheap")
    val onlyGood2 = Node.claim(onlyGood.id, onlyGood.statement, onlyGood.why)(
      forall((l: Term[List[Item.T]], x: Term[Item.T]) => shown(l, x) === (l.contains(x) && good2(x))))
    assertEquals(Desk(shelfKb).acceptAll.withKb(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood2, books, picking)).state(onlyGood2), ReviewState.Review)
    val d = Desk(shelfKb).acceptAll.withKb(kbOf((thick :: shelfNodes.filterNot(_ eq books)) :+ pick))
    // what does not use the term rests on what does: the root, whose meaning moved
    assertEquals(List("Books", "OnlyGood", "FromList").map(d.causes), List(List("self"), List("above"), List("above")))
  }

  test("a definition with an alternative: what uses the term waits for the choice, and the choice is in force") {
    val other = Node.definition("Thick", "A book is good when it is thick.", why = "Readers want long reads.")(good := ((b: Term[Book]) => b.pages >= 500))
    val d = Desk(shelfWith(pick, other))
    assert(Graph.alternatives(d.node("Thick").node, d.node("Books").node))
    val d2 = ok(d.accept(books, "Length is what readers asked for."))
    assertEquals((d2.state(other), d2.analysis.generate.undecided, d2.analysis.generate.inForce.get("good").map(_.id)),
      (ReviewState.Rejected, Set.empty[String], Some("Books")))
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

  test("a node whose code calls another contract's operation rests on that contract") {
    val promise2 = Node.contract(picks)("PickPromise", "A call returns only long enough books, from the shelf.", why = pickPromise.why)(
      (shelf, n, picked) => picked.forall(b => b.pages >= minPages && shelf.contains(b)))
      .examples(minPages.bind(100))(
        expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
        reject(List(Book("Short", 20)), 5, List(Book("Short", 20)), "never a short one"))
    val kb = KnowledgeBase("Calls", idea = "IDEA.md")(pickedAgain, againC, promise2).implementProven(promise2)(longOnes).implementProven(againC)(viaPick)
    val d = Desk(callsKb).acceptAll.withKb(kb)
    assertEquals(Graph(d.analysis.snapshot).restsOn(d.node("Again").node), ids("PickedAgain", "PickPromise"))
    assertEquals((d.causes("Again"), d.node("Again").node.relies), (List("above"), ids("PickPromise")))
  }

  test("any node may name a section of the idea; a section no node names is a warning") {
    val long2 = Node.claim("OnlyLong", onlyLong.statement, onlyLong.why, idea = "Picking")(
      forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).forall(b => b.pages >= minPages))).under(onlyGood)
    val d = Desk(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, books, picking, long2))
      .withIdea("# Shelf\n\nPick good items.\n\n## Picking\n\nPick only long books.\n\n## Selling\n\nSell them.\n\n## Not modelled\n\n- Prices.\n")
    assert(d.node("OnlyLong").node.content.str("notModelled").exists(_.contains("Prices")))
    assert(d.node("OnlyLong").node.content.str("idea").exists(_.contains("Pick only long books")))
    assert(d.node("OnlyGood").node.content.str("idea").exists(i => i.contains("Pick good items") && !i.contains("long books")))
    val warnings = Governance.warnings(d.analysis)
    assert(warnings.exists(_.contains("the section \"Selling\"")), warnings)
    assert(!warnings.exists(_.contains("the section \"Picking\"")), warnings)
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

  /** The shelf's nodes and more, with Pick implemented as in `shelfKb`. */
  private def shelfAnd(ns: Node[?]*) = kbOf(shelfNodes ++ ns).implement(pick)((shelf, n) => shelf.filter(_.pages >= minPages.value))
  private val newPart = Node.claim("Bounded", "At most n books are picked.", why = "Readers want few books.")(
    forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).length <= n)).under(fromList)

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

  test("a node placed under a second parent: that parent reviews its parts; the node rests on more, and says the same") {
    // A diamond: D a part of B and of C, both parts of A; before, D a part of B only.
    def diamond(dUnderC: Boolean): List[Node[?]] =
      val a = Node.claim("A", "Results are never negative.", why = "The purpose.")(forall((x: Term[BigInt]) => sq(x) >= 0))
      val b = Node.claim("B", "Results are at least zero.", why = "Zero is the floor.")(forall((x: Term[BigInt]) => sq(x) >= 0)).under(a)
      val c = Node.claim("C", "Results are zero or more.", why = "Said otherwise.")(forall((x: Term[BigInt]) => sq(x) >= 0)).under(a)
      val d = Node.claim("D", "The result is the square of the input.", why = "Squares are never negative.")(forall((x: Term[BigInt]) => sq(x) === x * x))
      List(a, b, c, if dUnderC then d.under(b, c) else d.under(b))
    val d = Desk(kbOf(diamond(dUnderC = false))).acceptAll.withKb(kbOf(diamond(dUnderC = true)))
    assertEquals(List("A", "B", "C", "D").map(d.causes), List(Nil, Nil, List("parts"), List("above")))
    val snap = proven(d.analysis.snapshot)
    // both mechanical: Lean proves C's parts make it, and D says what it said
    assertEquals(List("C", "D").map(id => Reading(snap, d.ledger).mechanical(snapOf(snap)(id))), List(None, None))
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
