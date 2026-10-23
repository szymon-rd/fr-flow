package frflow
package check

import frflow.lean.*
import frflow.ledger.*
import frflow.fixtures.*
import frflow.protocol.{NodeKind as Kind, *}
import io.circe.Json
import io.circe.syntax.*
import java.nio.file.Files

/** The snapshot, the developer's decisions and how drift shows, without Lean. */
class SnapshotSuite extends munit.FunSuite:

  private def workspace(): Workspace =
    val ws = Workspace(Files.createTempDirectory("frflow"), "../lean")
    Files.writeString(ws.root.resolve("IDEA.md"), "# Shelf\n\nPick good items.\n\n## Not modelled\n\n- Prices.\n")
    ws
  private def workflow(kb: KnowledgeBase = shelfKb, ws: Workspace = workspace()) = Workflow(kb, ws)

  private def nodes(a: Annotated): Map[String, Reviewed] = a.nodes.map(r => r.id.value -> r).toMap
  private def snapOf(s: Snapshot): Map[String, SnapNode] = s.nodes.map(n => n.id.value -> n).toMap
  private def ids(xs: String*): List[NodeId] = xs.map(NodeId(_)).toList
  private def words[A](xs: Seq[A]): List[String] = xs.map(_.toString).toList
  private def causes(r: Reviewed): List[String] = words(r.review.causes)
  private def belowIds(r: Reviewed): List[String] = words(r.review.below.map(_.id))
  private def str(s: String): Json = Json.fromString(s)
  private def notAccepted(w: Workflow) = w.kb.ordered.map(n => n.id -> w.state(n).toString).filter(_._2 != "accepted")
  private def req(node: String, by: String, reason: String, reject: List[String] = Nil, revisit: List[String] = Nil,
      confirm: List[String] = Nil, action: Action = Action.Accept, seen: String = "") =
    DecisionRequest(NodeId(node), by, reason, ids(reject*), ids(revisit*), ids(confirm*), action, Option(seen).filter(_.nonEmpty))
  private def ok(e: Either[String, Unit]): Unit = assert(e.isRight, e)
  private def accept(w: Workflow, n: Node[?], reason: String, rejecting: List[Node[?]] = Nil, confirm: List[Node[?]] = Nil) =
    w.decide(req(n.id, "dev", reason, rejecting.map(_.id), confirm = confirm.map(_.id)))
  private def acceptAll(w: Workflow): Unit =
    w.kb.ordered.foreach(n => ok(accept(w, n, s"${n.id} is right")))

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

  test("the snapshot is the DAG of the Scala definitions: parents, parts, definitions, the root") {
    val a = workflow().annotated
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
    assertEquals(ns("OnlyGood").split.map(_.complete.status), Some(ObligationStatus.Unchecked))
    assertEquals(ns("OnlyGood").split.map(_.needed.map(_.id)), Some(ids("FromList", "OnlyLong", "EveryLong")))
    assertEquals(ns("Pick").split, None)
    assertEquals(nodes(a)("FromList").state, ReviewState.Proposed)
    assertEquals(ns("Pick").examples.flatMap(_.implementation), List("ok", "ok", "ok", "ok"))
    assertEquals(ns("Pick").examples.head.`given`, List("minPages = 100"))
    assertEquals(ns("Pick").code, None) // its implementation lives in the model's own file
    // the model's files are where its nodes are written; a model may span several
    assertEquals(shelfKb.modelFiles.map(f => java.nio.file.Paths.get(f).getFileName.toString), List("Fixtures.scala"))
    assert(Reports.tree(a).contains("Pick (contract)  [proposed, unchecked, examples 4/4, code checked by running] (also under OnlyLong, EveryLong)"), Reports.tree(a))
  }

  test("the DAG is decided from the root down; a part waits for all its parents and the definitions it uses") {
    val w = workflow()
    assert(accept(w, fromList, "because it is right").left.exists(_.contains("accept OnlyGood first")))
    assert(accept(w, onlyGood, "because it is right").left.exists(_.contains("accept Books first")))
    assert(accept(w, books, " ").left.exists(_.contains("reason")))
    List(books, picking, onlyGood, fromList).foreach(n => ok(accept(w, n, s"${n.id} is right")))
    assert(accept(w, pick, "Pick is right").left.exists(_.contains("accept OnlyLong first")))
    List(onlyLong, everyLong, pick).foreach(n => ok(accept(w, n, s"${n.id} is right")))
    assert(w.kb.nodes.forall(w.state(_) == ReviewState.Accepted))
  }

  test("choosing one proposal rejects the alternatives it replaces; they are kept through later decisions") {
    val ws = workspace()
    val alt = Node.claim("Bounded", "Picked books come from the shelf, at most n of them.", why = "Readers want few books.")(
      forall((l: List[Book], n: Int) => picks(l, n).forall(b => l.contains(b)))).under(onlyGood).replaces(fromList)
    val w = workflow(shelfWith(pick, alt), ws)
    List(books, picking, onlyGood).foreach(n => ok(accept(w, n, s"${n.id} is right")))
    ok(accept(w, fromList, "Books must come from the shelf.", List(alt)))
    assertEquals((w.state(fromList), w.state(alt)), (ReviewState.Accepted, ReviewState.Rejected))
    assert(w.context(pick).contains("Rejected alternative Bounded"), w.context(pick))
    // parts of one parent are not alternatives: together they make it
    assert(accept(w, onlyLong, "parts are not alternatives", List(everyLong)).left.exists(_.contains("not an alternative")))
    // the agent removes the rejected node, then rewords FromList; the new decision keeps the alternative
    val reworded = Node.claim("FromList", "Every picked book is on the shelf.", why = fromList.why)(
      forall((l: List[Book], n: Int) => picks(l, n).forall(b => l.contains(b)))).under(onlyGood)
    val w2 = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, books, picking, reworded), ws)
    assertEquals(w2.state(reworded), ReviewState.Review)
    ok(accept(w2, reworded, "The wording is clearer."))
    assertEquals(nodes(w2.annotated)("FromList").review.decision.map(_.reason), Some("Books must come from the shelf."))
    assertEquals(w2.ledger.alternatives(NodeId("FromList")).map(_._1), ids("Bounded"))
    assertEquals(w2.ledger.history(NodeId("FromList")).map(_.action.toString), List("accept", "accept"))
  }

  test("a change to the idea's lead reviews the root only") {
    val ws = workspace()
    val w = workflow(shelfKb, ws)
    acceptAll(w)
    Files.writeString(ws.root.resolve("IDEA.md"), "# Shelf\n\nPick good items, quickly.\n\n## Not modelled\n\n- Prices.\n")
    assertEquals(notAccepted(w), List("OnlyGood" -> "review"))
    assert(nodes(w.annotated)("OnlyGood").node.content.str("idea").exists(_.contains("quickly")))
  }

  test("after a change, the developer names the decisions below that it may affect; a shared part is listed once") {
    val ws = workspace()
    val w = workflow(shelfKb, ws)
    acceptAll(w)
    Files.writeString(ws.root.resolve("IDEA.md"), "# Shelf\n\nPick good items, quickly.\n\n## Not modelled\n\n- Prices.\n")
    assertEquals(belowIds(nodes(w.annotated)("OnlyGood")).count(_ == "Pick"), 1)
    ok(w.decide(req("OnlyGood", "dev", "Picking must be quick now.", revisit = List("Pick"))))
    assert(w.decide(req("FromList", "dev", "OnlyGood is not below it.", revisit = List("OnlyGood"))).left.exists(_.contains("not among")))
    assertEquals(notAccepted(w), List("Pick" -> "review"))
    assertEquals(causes(nodes(w.annotated)("Pick")), List("revisit"))
    ok(accept(w, pick, "Filtering a list is quick enough."))
    assertEquals(w.ledger.history(NodeId("Pick")).map(_.action.toString), List("accept", "revisit", "confirm"))
    assertEquals(nodes(w.annotated)("Pick").review.decision.map(_.reason), Some("Pick is right"))
    assert(w.context(pick).contains("To revisit (dev): OnlyGood changed"))
  }

  test("a proposal can be rejected on its own; a reason takes a few words") {
    val alt = Node.claim("Bounded", "Picked books come from the shelf, at most n of them.", why = "Readers want few books.")(
      forall((l: List[Book], n: Int) => picks(l, n).forall(b => l.contains(b)))).under(onlyGood).replaces(fromList)
    val w = workflow(shelfWith(pick, alt))
    assert(accept(w, books, "ok").left.exists(_.contains("few words")))
    List(books, picking, onlyGood).foreach(n => ok(accept(w, n, s"${n.id} is right")))
    ok(w.decide(req("Bounded", "dev", "Readers want every good book.", action = Action.Reject)))
    assertEquals((w.state(alt), w.state(fromList)), (ReviewState.Rejected, ReviewState.Proposed))
    assert(w.decide(req("OnlyGood", "dev", "The root is not a proposal.", action = Action.Reject)).left.exists(_.contains("only a proposal")))
  }

  test("rejecting a node puts what rests on it up for review, and status fails until it is moved") {
    val alt = Node.claim("Bounded", "Picked books come from the shelf, at most n of them.", why = "Readers want few books.")(
      forall((l: List[Book], n: Int) => picks(l, n).forall(b => l.contains(b)))).under(onlyGood).replaces(fromList)
    val w = workflow(shelfWith(pick, alt))
    shelfKb.ordered.foreach(n => ok(accept(w, n, s"${n.id} is right")))
    ok(accept(w, alt, "Readers want fewer books now.", List(fromList)))
    assertEquals(w.state(fromList), ReviewState.Rejected)
    assertEquals(causes(nodes(w.annotated)("Pick")), List("above"))
    assert(accept(w, pick, "Pick still holds here.").left.exists(_.contains("accept FromList first")))
    val (text, settled) = w.status
    assert(!settled)
    assert(text.contains("FromList (claim)  [rejected: remove it from the model"), text)
    assert(Reports.inbox(Some(w.annotated), Nil).contains("Pick: rests on rejected FromList"))
    // The agent reads why: the reason may ask for something in the node's place.
    val inbox = Reports.inbox(Some(w.annotated), Nil)
    assert(inbox.contains("FromList: rejected by dev: Bounded was chosen instead: Readers want fewer books now; propose what the reason asks for"), inbox)
    assert(w.context(fromList).contains("Rejected by dev at "), w.context(fromList))
  }

  test("a node can opt out of Lean: Scala only, decided by reading, examples still run") {
    // `mkString` is outside the Scala the macro translates; an informal node may use any Scala.
    val titled = Node.contract(picks)("Titled", "Picked books have a title.", why = "Titles are free text; not worth a proof.", formal = false)(
      (shelf, n, picked) => picked.forall(b => b.title.mkString.nonEmpty && long(b))).under(shelfParts*)
      .examples(minPages.bind(100))(
        expect(List(Book("Long", 300)), 1, List(Book("Long", 300)), "a titled book"),
        expect(Nil, 1, Nil, "nothing to pick"),
        reject(List(Book("", 300)), 1, List(Book("", 300)), "a book without a title"))
    val kb = shelfWith(titled)
    assertEquals(kb.problems, Nil)
    val w = workflow(kb)
    val ns = nodes(w.annotated)
    val n = ns("Titled")
    assertEquals(n.node.status.map(_.toString), Some("informal"))
    assertEquals(n.node.content("formal"), Some(Json.False))
    assertEquals(n.node.examples.map(_.contract), List("ok", "ok", "ok"))
    assert(!w.generate.formal(titled))
    assert(n.node.content("sources").flatMap(_.hcursor.downField("post").as[String].toOption).exists(_.contains("mkString")), n)
    // what it refers to is still part of what it is decided on
    assert(n.node.content.strs("uses").exists(_.startsWith("long = ")), n)
    // its parents' splits are decided by reading: Lean cannot state them
    assertEquals(ns("FromList").node.split.map(_.complete.status.toString), Some("informal"))
  }

  test("how the implementation is built is part of the contract's content") {
    assertEquals(shelfKb.implementation(pick).map(_.wiring), Some("(shelf, n) => shelf.filter(_.pages >= minPages.value)"))
    val w = workflow()
    assertEquals(nodes(w.annotated)("Pick").node.content.str("implementation"), Some("(shelf, n) => shelf.filter(_.pages >= minPages.value)"))
  }

  test("a decision is refused when the node moved since the developer looked at it") {
    val w = workflow()
    assert(w.decide(req("Books", "dev", "It is the idea.", seen = "stale")).left.exists(_.contains("changed since")))
    val seen = nodes(w.annotated)("Books").review.version
    ok(w.decide(req("Books", "dev", "It is the idea.", seen = seen)))
  }

  test("repeated content is written once and survives a merge that interleaves entries") {
    val c1 = Content("statement" -> str("one"))
    val c2 = Content("statement" -> str("two"))
    def d(c: Content, r: String) = Decision(Action.Accept, "dev", r, r, content = c)
    val l = Ledger(Map(NodeId("A") -> List(d(c1, "1"), d(c2, "2"), d(c1, "3"))))
    val text = Canonical.file(l.asJson)
    assert(text.contains("same:"))
    assertEquals(io.circe.parser.decode[Ledger](text), Right(l))
  }

  test("when two branches decided the same node and both were kept, it is decided again") {
    val w = workflow()
    ok(accept(w, books, "it is the idea"))
    val base = w.ledger
    val b = NodeId("Books")
    def d(r: String) = Decision(Action.Accept, "dev", r, r, content = base.history(b).head.content)
    val ours = base.add(b, d("on branch one"))
    val theirs = base.add(b, d("on branch two"))
    val merged = Ledger(Map(b -> (ours.history(b) :+ theirs.history(b).last)))
    assert(merged.forked(b))
    assert(!merged.add(b, d("decided again after the merge")).forked(b))
  }

  test("decisions below are confirmed by name, only below nodes that are accepted") {
    val ws = workspace()
    acceptAll(workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(under(onlyGood)*), ws))
    val r2 = root2
    val now = under(r2, "Picked books come from the shelf, and nowhere else.")
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(now*), ws)
    // FromList changed itself, so it is decided on its own; nothing below it is listed with the root
    assert(accept(w, r2, "Clearer with 'only then' added.", confirm = List(now(3), now(5))).left.exists(_.contains("not among")))
    // (the definitions are listed too: a change of the purpose may affect any decision)
    assertEquals(belowIds(nodes(w.annotated)("OnlyGood")), List("OnlyLong", "Books", "Picking"))
    ok(accept(w, r2, "Clearer with 'only then' added."))
    assertEquals(notAccepted(w).map(_._1), List("FromList", "OnlyLong", "Pick"))
  }

  test("the definition as written runs past comments between its chained calls, and not into the next one's") {
    val d = workflow().definition(longPick)
    assert(d.startsWith("val longPick = ") && d.contains(".examples(") && d.endsWith("\"never a short one\"))"), d)
  }

  test("a change to a node's meaning shows below, and what still holds is confirmed by name") {
    val ws = workspace()
    acceptAll(workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(under(onlyGood)*), ws))
    val r2 = root2
    val now = under(r2)
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(now*), ws)
    val ns = nodes(w.annotated)
    assertEquals(causes(ns("OnlyGood")), List("self"))
    assertEquals(causes(ns("FromList")), List("above"))
    assertEquals(causes(ns("Pick")), List("above"))
    assertEquals(ns("OnlyGood").review.below.map(b => b.id.value -> b.kind.toString),
      List("FromList" -> "moved", "OnlyLong" -> "moved", "Pick" -> "moved", "Books" -> "accepted", "Picking" -> "accepted")) // parents first
    ok(accept(w, r2, "Clearer with 'only then' added.", confirm = List(now(3), now(4), now(5))))
    assert(w.kb.nodes.forall(w.state(_) == ReviewState.Accepted), w.kb.nodes.map(w.state))
    assertEquals(w.ledger.history(NodeId("Pick")).map(_.action.toString), List("accept", "confirm"))
    assert(w.context(now(5)).contains("Chosen by dev because: Pick is right"))
  }

  test("a statement reworded, its formula unchanged, reviews that node only; what is below is listed under it, not sent to review") {
    val ws = workspace()
    acceptAll(workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(under(onlyGood)*), ws))
    val now = under(rootReworded)
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(now*), ws)
    assertEquals(notAccepted(w), List("OnlyGood" -> "review"))
    val ns = nodes(w.annotated)
    assertEquals(causes(ns("OnlyGood")), List("self"))
    // what may be affected: the decisions below it, each to revisit by name if it is
    assertEquals(ns("OnlyGood").review.below.map(b => b.id.value -> b.kind.toString),
      List("FromList" -> "accepted", "OnlyLong" -> "accepted", "Pick" -> "accepted", "Books" -> "accepted", "Picking" -> "accepted"))
    assertEquals(ns("Pick").review.moved, Nil)
    ok(accept(w, rootReworded, "Clearer with 'only then' added."))
    assert(w.kb.nodes.forall(w.state(_) == ReviewState.Accepted), w.kb.nodes.map(w.state))
    // after it, a change of its formula still moves what is below
    val w2 = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(under(root2)*), ws)
    assertEquals(causes(nodes(w2.annotated)("Pick")), List("above"))
    // a node out of Lean is its words: rewording it moves what is below
    val ws3 = workspace()
    def informal(statement: String) = Node.claim("Informal", statement, why = "w", formal = false)(forall((x: BigInt) => sq(x) >= 0))
    def kb3(statement: String) =
      val top = informal(statement)
      KnowledgeBase("Team", idea = "IDEA.md")(top, Node.claim("Floor", "Results are at least zero.", why = "w")(forall((x: BigInt) => sq(x) >= 0)).under(top))
    acceptAll(workflow(kb3("Results are never negative."), ws3))
    assertEquals(causes(nodes(workflow(kb3("Results are never below zero."), ws3).annotated)("Floor")), List("above"))
  }

  test("what is not modelled can change without disturbing decisions") {
    val ws = workspace()
    val w = workflow(shelfKb, ws)
    acceptAll(w)
    Files.writeString(ws.root.resolve("IDEA.md"), "# Shelf\n\nPick good items.\n\n## Not modelled\n\n- Prices.\n- Covers.\n")
    // only the root is reviewed: what is not modelled narrows nothing below it
    assertEquals(notAccepted(w), List("OnlyGood" -> "review"))
  }

  test("a decided node removed from the model shows until the removal is confirmed") {
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(shelfNodes*), ws)
    assertEquals(w.gone, ids("Pick"))
    assert(w.status._1.contains("Pick  [review: gone]"))
    ok(w.decide(req("Pick", "dev", "Picking moved to another service.")))
    assertEquals(w.gone, Nil)
  }

  test("a change to the implementation's code shows on its contract") {
    val ws = workspace()
    val impl = Files.createTempDirectory("impl").resolve("Impl.scala")
    Files.writeString(impl, "class Impl")
    val kb = shelfKb.withImplementation(Implementation("Pick", () => (s: List[Book], n: Int) => s.filter(_.pages >= 100), List(impl.toString, "Model.scala")))
    val w = workflow(kb, ws)
    acceptAll(w)
    assertEquals(Some(nodes(w.annotated)("Pick").state.toString), Some("accepted"))
    Files.writeString(impl, "class Impl // faster")
    assertEquals(causes(nodes(w.annotated)("Pick")), List("code"))
    assert(w.status._1.contains("review: code"))
    ok(w.decide(req("Pick", "dev", "Same behaviour; examples pass.")))
    assertEquals(Some(nodes(w.annotated)("Pick").state.toString), Some("accepted"))
  }

  test("a design decision governs files, sits under what it serves, and has nothing to prove") {
    val ws = workspace()
    Files.writeString(ws.root.resolve("Store.scala"), "object Store")
    val cache = Node.design("Cache", "Shelves are cached in memory.", why = "They change once a day.")("Store.scala").under(pick)
    val w = workflow(shelfWith(pick, cache), ws)
    assertEquals(w.kb.problems, Nil)
    acceptAll(w)
    assertEquals(nodes(w.annotated)("Cache").node.split, None)
    assertEquals(nodes(w.annotated)("Cache").node.status, None)
    Files.writeString(ws.root.resolve("Store.scala"), "object Store // redis")
    assertEquals(causes(nodes(w.annotated)("Cache")), List("code"))
  }

  test("the ledger is the history; a contract shows what it does not promise") {
    val w = workflow(callsKb)
    ok(accept(w, pickedAgain, "it is the idea"))
    assertEquals(w.ledger.all.map(_._1), ids("PickedAgain"))
    assertEquals(nodes(w.annotated)("PickedAgain").review.decision.map(_.by), Some("dev"))
    assert(nodes(w.annotated)("PickPromise").node.limits.exists(_.contains("empty result")))
    assert(Files.isRegularFile(w.writeSnapshot()))
  }

  test("a change to what a term means reviews the nodes that use it") {
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val good2 = Param[Item.T => Boolean]("good", "whether an item is cheap")
    val onlyGood2 = Node.claim(onlyGood.id, onlyGood.statement, onlyGood.why)(
      forall((l: List[Item.T], x: Item.T) => shown(l, x) == (l.contains(x) && good2(x))))
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood2, books, picking), ws)
    assertEquals(w.state(onlyGood2), ReviewState.Review)
  }

  test("a change to a definition reviews the nodes that use its terms") {
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val thick = Node.definition("Books", "Items are books; a book is good when it is thick.", why = books.why)(
      Item := of[Book], good := ((b: Book) => b.pages >= 500))
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(((thick :: shelfNodes.filterNot(_ eq books)) :+ pick)*), ws)
    val ns = nodes(w.annotated)
    assertEquals(causes(ns("Books")), List("self"))
    assertEquals(causes(ns("OnlyGood")), List("above"))
    // what does not use the term rests on what does: the root, whose meaning moved
    assertEquals(causes(ns("FromList")), List("above"))
  }

  test("a definition with an alternative: what uses the term waits for the choice, and the choice is in force") {
    val ws = workspace()
    val thick = Node.definition("Thick", "A book is good when it is thick.", why = "Readers want long reads.")(good := ((b: Book) => b.pages >= 500))
    val w = workflow(shelfWith(pick, thick), ws)
    assertEquals(w.generate.undecided, Set("good"))
    assertEquals(nodes(w.annotated)("Thick").node.defines, List("good"))
    assert(Decisions.alternatives(nodes(w.annotated)("Thick").node, nodes(w.annotated)("Books").node))
    ok(accept(w, books, "Length is what readers asked for.", List(thick)))
    assertEquals(w.state(thick), ReviewState.Rejected)
    assertEquals(w.generate.undecided, Set.empty[String])
    assertEquals(w.generate.inForce.get("good").map(_.id), Some("Books"))
  }

  test("the ledger is compact on disk") {
    val ws = workspace()
    val w = workflow(shelfKb, ws)
    acceptAll(w)
    val committed = w.ledger
    val text = Files.readString(ws.ledgerFile)
    assertEquals(io.circe.parser.decode[Ledger](text), Right(committed))
  }

  // Lean is not run here: these mark every node as Lean would.
  private def proven(s: Snapshot): Snapshot = s.copy(nodes = s.nodes.map(n => n.copy(
    status = n.status.map(_ => CheckStatus.Proven),
    split = n.split.map(_ => Split(Outcome(ObligationStatus.Proven, "auto"), Nil, Outcome(ObligationStatus.NoClash))))))
  /** The snapshot with one node's content changed (and its hash with it). */
  private def changing(s: Snapshot, id: String)(f: PartialFunction[(String, Json), (String, Json)]): Snapshot =
    s.copy(nodes = s.nodes.map(n => if n.id != NodeId(id) then n else
      val c = n.content.mapFields(f)
      n.copy(content = c, hash = c.hash)))

  test("a decision is mechanical only where Lean proves it again and nothing in it is a choice; the agent decides nothing") {
    val w = workflow()
    val snap = proven(w.baseSnapshot)
    val ns = snapOf(snap)
    def at(i: Int) = f"2026-01-01T00:00:$i%02dZ"
    def decide(l: Ledger, id: String, action: Action, i: Int, by: String = "dev") =
      Decisions.decide(snap, l, req(id, by, s"$id holds for this reason", action = action), at(i)).left.map(_.message)
    val l1 = List("Books", "Picking", "OnlyGood").zipWithIndex.foldLeft(Ledger.empty)((l, x) => decide(l, x._1, Action.Accept, x._2 + 1).toOption.get)
    assert(Decisions.mechanical(snap, l1, ns("Books")).exists(_.contains("definition nodes hold a choice")))
    // a proposal is the developer's choice
    assert(Decisions.mechanical(snap, l1, ns("FromList")).exists(_.contains("only a node under review")))
    // the developer accepts or rejects: a confirmation follows from an acceptance
    assert(decide(l1, "FromList", Action.Confirm, 5, "agent").left.exists(_.contains("unknown decision")))
  }

  test("deciding a large tree stays fast: each node's state is computed once") {
    // 800 nodes, eight children per node, all accepted
    val ns = (0 until 800).toList.map { i =>
      val c = Content("statement" -> str(s"node $i"))
      SnapNode(NodeId(s"N$i"), Kind.Claim, c, c.hash, parents = if i == 0 then Nil else ids(s"N${(i - 1) / 8}"))
    }
    val snap = Snapshot("Large", ns)
    val ledger = ns.foldLeft(Ledger.empty)((l, n) => l.add(n.id, Decision(Action.Accept, "dev", "2026-01-01T00:00:00Z", "it is right",
      chain = Decisions.parentChain(snap, n), content = n.content)))
    val t = System.nanoTime
    val a = Decisions.annotate(snap, ledger)
    val seconds = (System.nanoTime - t) / 1e9
    assert(a.nodes.forall(_.state == ReviewState.Accepted), a.nodes.head)
    assert(seconds < 5, s"$seconds s")
  }

  test("rejecting a proposal rejects what rests on it; a reworded why is the theory, not mechanical, and does not cascade") {
    val w = workflow()
    val snap = proven(w.baseSnapshot)
    def at(i: Int) = f"2026-01-01T00:01:$i%02dZ"
    def decide(s: Snapshot, l: Ledger, id: String, action: Action, i: Int, by: String = "dev") =
      Decisions.decide(s, l, req(id, by, s"$id holds for this reason", action = action), at(i)).left.map(_.message)
    val l1 = List("Books", "Picking", "OnlyGood").zipWithIndex.foldLeft(Ledger.empty)((l, x) => decide(snap, l, x._1, Action.Accept, x._2 + 1).toOption.get)
    val rejected = decide(snap, l1, "FromList", Action.Reject, 5).fold(e => fail(e), identity)
    assertEquals(ids("FromList", "Pick").map(rejected.current(_).map(_.action)), List.fill(2)(Some(Action.Reject)))
    // all accepted; then only FromList's why is reworded
    val all = List("FromList", "OnlyLong", "EveryLong", "Pick").zipWithIndex.foldLeft(l1)((l, x) => decide(snap, l, x._1, Action.Accept, 10 + x._2).fold(e => fail(e), identity))
    val reworded = changing(snap, "FromList") { case ("why", _) => "why" -> str("Reworded, saying the same.") }
    val rs = snapOf(reworded)
    assertEquals(Decisions.causes(reworded, all, rs("FromList")), List(Cause.Self))
    assert(Decisions.mechanical(reworded, all, rs("FromList")).isDefined)
    assert(Decisions.causes(reworded, all, rs("Pick")).isEmpty) // a why does not cascade
  }

  test("a node whose code calls another contract's operation rests on that contract") {
    val ws = workspace()
    acceptAll(workflow(callsKb, ws))
    val promise2 = Node.contract(picks)("PickPromise", "A call returns only long enough books, from the shelf.", why = pickPromise.why)(
      (shelf, n, picked) => picked.forall(b => b.pages >= minPages.value && shelf.contains(b)))
      .examples(minPages.bind(100))(
        expect(List(Book("Long", 300), Book("Short", 20)), 5, List(Book("Long", 300)), "only the long book"),
        reject(List(Book("Short", 20)), 5, List(Book("Short", 20)), "never a short one"))
    val kb = KnowledgeBase("Calls", idea = "IDEA.md")(pickedAgain, againC, promise2).implementProven(promise2)(longOnes).implementProven(againC)(viaPick)
    val w = workflow(kb, ws)
    assertEquals(w.restsOn(againC).map(_.id), List("PickedAgain", "PickPromise"))
    val ns = nodes(w.annotated)
    assertEquals(causes(ns("Again")), List("above"))
    assertEquals(ns("Again").node.relies, ids("PickPromise"))
    assert(w.context(againC).contains("## Its code calls"), w.context(againC))
    assert(w.context(promise2).contains("Rests on it besides its parts"), w.context(promise2))
  }

  test("source files no node governs are found outside src/main too; tests are not production code") {
    val ws = workspace()
    Files.createDirectories(ws.root.resolve("src/fast/scala"))
    Files.writeString(ws.root.resolve("src/fast/scala/Leak.scala"), "object Leak")
    Files.createDirectories(ws.root.resolve("src/test/scala"))
    Files.writeString(ws.root.resolve("src/test/scala/T.scala"), "object T")
    val u = workflow(shelfKb, ws).ungoverned
    assert(u.contains("src/fast/scala/Leak.scala"), u)
    assert(!u.exists(_.contains("src/test")), u)
  }

  test("any node may name a section of the idea; a section no node names is a warning") {
    val ws = workspace()
    Files.writeString(ws.root.resolve("IDEA.md"),
      "# Shelf\n\nPick good items.\n\n## Picking\n\nPick only long books.\n\n## Selling\n\nSell them.\n\n## Not modelled\n\n- Prices.\n")
    val long2 = Node.claim("OnlyLong", onlyLong.statement, onlyLong.why, idea = "Picking")(
      forall((l: List[Book], n: Int) => picks(l, n).forall(b => b.pages >= minPages.value))).under(onlyGood)
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, books, picking, long2), ws)
    assert(nodes(w.annotated)("OnlyLong").node.content.str("notModelled").exists(_.contains("Prices")))
    assert(nodes(w.annotated)("OnlyLong").node.content.str("idea").exists(_.contains("Pick only long books")))
    assert(nodes(w.annotated)("OnlyGood").node.content.str("idea").exists(i => i.contains("Pick good items") && !i.contains("long books")))
    assert(w.codeWarnings.exists(_.contains("the section \"Selling\"")), w.codeWarnings)
    assert(!w.codeWarnings.exists(_.contains("the section \"Picking\"")), w.codeWarnings)
  }

  test("with no developer key, status fails whatever the ledger says") {
    val w = workflow()
    acceptAll(w)
    assert(w.integrity.exists(_.startsWith("no developer key")), w.integrity)
    assert(!w.status._2)
  }

  test("a confirmation it cannot apply is refused, with why, not dropped") {
    val ws = workspace()
    acceptAll(workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(under(onlyGood)*), ws))
    val r2 = root2
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(under(r2)*), ws)
    val r = w.decide(req("OnlyGood", "dev", "Clearer with 'only then' added.", confirm = List("Books")))
    assert(r.left.exists(_.contains("Books")), r)
    val h = w.decide(req("OnlyGood", "dev", "Clearer with only then added.", revisit = List("Elsewhere")))
    assert(h.left.exists(_.contains("not among")), h)
    ok(w.decide(req("OnlyGood", "dev", "Clearer with 'only then' added.", revisit = List("FromList"))))
  }

  test("a type change is mechanical where nothing the developer decided changed") {
    val w = workflow()
    acceptAll(w)
    val snap = proven(w.baseSnapshot)
    def withUses(f: Vector[Json] => Vector[Json]) =
      changing(snap, "Pick") { case ("uses", u) => "uses" -> Json.fromValues(f(u.asArray.getOrElse(Vector.empty))) }
    // Book gains a field: only the types Pick uses changed, and how its examples print
    val changed = withUses(_.map(u => if u.asString.exists(_.startsWith("case class Book")) then str("case class Book(title: String, pages: Int, author: String)") else u))
    val pickNode = snapOf(changed)("Pick")
    assertEquals(Decisions.state(changed, w.ledger, pickNode), ReviewState.Review)
    assertEquals(Decisions.mechanical(changed, w.ledger, pickNode), None)
    // a definition it calls is part of what it says: not mechanical
    val redefined = withUses(_ :+ str("long = (b: Book) => b.pages >= 10"))
    assert(Decisions.mechanical(redefined, w.ledger, snapOf(redefined)("Pick")).exists(_.contains("changed")))
  }

  test("alternatives are a node and the one it replaces, or two definitions of one term; parts of one parent are not") {
    def n(id: String, kind: Kind = Kind.Claim, replaces: Option[String] = None, defines: List[String] = Nil) =
      SnapNode(NodeId(id), kind, Content.empty, Content.empty.hash, parents = if kind == Kind.Definition then Nil else ids("R"),
        replaces = replaces.map(NodeId(_)), defines = defines)
    val (a, b, c) = (n("A"), n("B", replaces = Some("A")), n("C"))
    val (d1, d2) = (n("D1", Kind.Definition, defines = List("good")), n("D2", Kind.Definition, defines = List("good", "Item")))
    assert(Decisions.alternatives(a, b) && Decisions.alternatives(b, a) && Decisions.alternatives(d1, d2))
    assert(!Decisions.alternatives(a, c) && !Decisions.alternatives(a, d1))
  }

  private def causesOf(w: Workflow, id: String) = causes(nodes(w.annotated)(id))
  private def kbOf(ns: Seq[Node[?]]) = KnowledgeBase("Shelf", idea = "IDEA.md")(ns*)
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
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val w = workflow(shelfAnd(pick, newPart), ws)
    assertEquals(causesOf(w, "FromList"), List("parts"))
    assertEquals(notAccepted(w), List("FromList" -> "review", "Bounded" -> "proposed"))
    assertEquals(nodes(w.annotated)("Bounded").review.waitsFor.map(_.value), Some("FromList"))
    // these parts make it: a confirmation, which keeps the reason it was chosen and binds the parts
    ok(accept(w, fromList, "FromList is still made by its parts."))
    assertEquals(w.ledger.history(NodeId("FromList")).map(_.action.toString), List("accept", "confirm"))
    assertEquals(nodes(w.annotated)("FromList").review.decision.map(_.reason), Some("FromList is right"))
    assertEquals(w.ledger.binding(NodeId("FromList")).get.content.strs("parts"), List("Pick", "Bounded"))
    ok(accept(w, newPart, "A bound helps readers."))
    assertEquals(w.kb.nodes.map(w.state).distinct, List(ReviewState.Accepted))
    // and removed: the parent again
    val back = workflow(shelfKb, ws)
    assertEquals(notAccepted(back), List("FromList" -> "review"))
    assertEquals(causesOf(back, "FromList"), List("parts"))
    assertEquals(back.gone, ids("Bounded"))
  }

  test("a change of parts is mechanical when Lean proves the parts make it, each needed; not otherwise") {
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val w = workflow(shelfAnd(pick, newPart), ws)
    val snap = proven(w.baseSnapshot)
    val ns = snapOf(snap)
    assertEquals(Decisions.causes(snap, w.ledger, ns("FromList")), List(Cause.Parts))
    assertEquals(Decisions.mechanical(snap, w.ledger, ns("FromList")), None)
    import ObligationStatus.{Needed, NotNeeded, Open, Proven}
    def withSplit(complete: ObligationStatus, needed: ObligationStatus) = snap.copy(nodes = snap.nodes.map(n => if n.id != NodeId("FromList") then n
      else n.copy(split = Some(Split(Outcome(complete), ids("Pick", "Bounded").map(Split.Part(_, needed, "")), Outcome(ObligationStatus.NoClash))))))
    def fromList(s: Snapshot) = snapOf(s)("FromList")
    assertEquals(Decisions.mechanical(withSplit(Proven, Needed), w.ledger, ns("FromList")), None)
    // a part not needed (Lean shows the parent without it), or the parts not shown to make it: the developer decides
    assert(Decisions.mechanical(withSplit(Proven, NotNeeded), w.ledger, fromList(withSplit(Proven, NotNeeded))).isDefined)
    assert(Decisions.mechanical(withSplit(Open, Needed), w.ledger, fromList(withSplit(Open, Needed))).isDefined)
    // a proposal is never mechanical
    assert(Decisions.mechanical(snap, w.ledger, ns("Bounded")).exists(_.contains("proposed")))
  }

  test("a diamond: the node under two parents is reviewed once, listed once after both, and confirmed once") {
    val ws = workspace()
    acceptAll(workflow(kbOf(diamond()), ws))
    val now = diamond("Results are never negative, whatever the input.")
    val w = workflow(kbOf(now), ws)
    assertEquals(List("A", "B", "C", "D").map(causesOf(w, _)), List(List("self"), List("above"), List("above"), List("above")))
    assertEquals(belowIds(nodes(w.annotated)("A")), List("B", "C", "D"))
    // D waits for its parents, which wait for A
    assert(accept(w, now(3), "D still holds.").left.exists(_.contains("accept B first")))
    assert(accept(w, now(2), "C still holds.").left.exists(_.contains("accept A first")))
    ok(accept(w, now(0), "Clearer about every input.", confirm = now.drop(1)))
    assertEquals(w.kb.nodes.map(w.state).distinct, List(ReviewState.Accepted))
    assertEquals(w.ledger.history(NodeId("D")).map(_.action.toString), List("accept", "confirm"))
  }

  test("a proposal waits for all of its parents") {
    val w = workflow(kbOf(diamond()))
    List("A", "B").foreach(id => ok(w.decide(req(id, "dev", s"$id is right"))))
    assertEquals(nodes(w.annotated)("D").review.waitsFor.map(_.value), Some("C"))
    assert(w.decide(req("D", "dev", "D is right")).left.exists(_.contains("accept C first")))
    ok(w.decide(req("C", "dev", "C is right")))
    ok(w.decide(req("D", "dev", "D is right")))
  }

  test("a node placed under a second parent: that parent reviews its parts; the node rests on more, and says the same") {
    val ws = workspace()
    acceptAll(workflow(kbOf(diamond(dUnderC = false)), ws))
    val w = workflow(kbOf(diamond()), ws)
    assertEquals(List("A", "B", "C", "D").map(causesOf(w, _)), List(Nil, Nil, List("parts"), List("above")))
    val snap = proven(w.baseSnapshot)
    // both mechanical: Lean proves C's parts make it, and D says what it said
    assertEquals(List("C", "D").map(id => Decisions.mechanical(snap, w.ledger, snapOf(snap)(id))), List(None, None))
  }

  test("a change to a definition lists what rests on it, however far down, each once, to confirm by name") {
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val thick = Node.definition("Books", "Items are books; a book is good when it is thick.", why = books.why)(
      Item := of[Book], good := ((b: Book) => b.pages >= 500))
    val now = (thick :: shelfNodes.filterNot(_ eq books)) :+ pick
    val w = workflow(kbOf(now).implement(pick)((shelf, n) => shelf.filter(_.pages >= minPages.value)), ws)
    assertEquals(belowIds(nodes(w.annotated)("Books")), List("OnlyGood", "FromList", "OnlyLong", "EveryLong", "Pick"))
    ok(accept(w, thick, "Readers want thick books now.", confirm = now.filter(n => Set("OnlyGood", "FromList", "OnlyLong", "EveryLong", "Pick")(n.id))))
    assertEquals(w.kb.nodes.map(w.state).distinct, List(ReviewState.Accepted))
  }

  test("the alternatives of each node in the model: what it replaces or is replaced by, other definitions of its terms; never its siblings") {
    val alt = Node.claim("Bounded", "Picked books come from the shelf, at most n of them.", why = "Readers want few books.")(
      forall((l: List[Book], n: Int) => picks(l, n).forall(b => l.contains(b)))).under(onlyGood).replaces(fromList)
    val thick = Node.definition("Thick", "A book is good when it is thick.", why = "Readers want long reads.")(good := ((b: Book) => b.pages >= 500))
    val ns = nodes(workflow(shelfWith(pick, alt, thick)).annotated)
    def rivals(id: String) = words(ns(id).review.rivals)
    assertEquals(List("FromList", "Bounded", "Books", "Thick", "OnlyLong").map(rivals), List(List("Bounded"), List("FromList"), List("Thick"), List("Books"), Nil))
  }

  test("placing a node under another parent changes where it rests, not what it says") {
    def node(parents: List[String], under: String) =
      val c = Content("kind" -> str("claim"), "parents" -> Json.fromValues(parents.map(str)), "parts" -> Json.arr(), "statement" -> str("The result is a square."),
        "definition" -> str(s"val d = Node.claim(\"D\", \"The result is a square.\", why = \"w\")(f)\n  .under($under)\n  .examples()()"))
      SnapNode(NodeId("D"), Kind.Claim, c, c.hash, parents = ids(parents*))
    val before = node(List("B"), "b")
    val ledger = Ledger.empty.add(NodeId("D"), Decision(Action.Accept, "dev", "2026-01-01T00:00:00Z", "it is right", content = before.content))
    val now = node(List("B", "C"), "b, c")
    assertEquals(Decisions.causes(Snapshot("S", List(now)), ledger, now), Nil)
    // what it says, changed beside the call that places it: itself
    val c = now.content.mapFields { case ("definition", d) => "definition" -> str(d.asString.getOrElse("").replace(".examples()()", ".examples()(expect(1))")) }
    val reworded = now.copy(content = c, hash = c.hash)
    assertEquals(Decisions.causes(Snapshot("S", List(reworded)), ledger, reworded), List(Cause.Self))
  }

