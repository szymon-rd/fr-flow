package frflow

import frflow.fixtures.*
import java.nio.file.Files

/** The snapshot, the developer's decisions and how drift shows, without Lean. */
class SnapshotSuite extends munit.FunSuite:

  private def workspace(): Workspace =
    val ws = Workspace(Files.createTempDirectory("frflow"), "../lean")
    Files.writeString(ws.root.resolve("IDEA.md"), "# Shelf\n\nPick good items.\n\n## Not modelled\n\n- Prices.\n")
    ws
  private def workflow(kb: KnowledgeBase = shelfKb, ws: Workspace = workspace()) = Workflow(kb, ws)

  private def nodes(j: Json) = j("nodes").get.arr.map(n => n("id").flatMap(_.str).get -> n).toMap
  private def field(n: Json, path: String*) = path.foldLeft(Option(n))((j, k) => j.flatMap(_(k))).flatMap(_.str)
  private def ok(e: Either[String, Unit]): Unit = assert(e.isRight, e)
  private def accept(w: Workflow, n: Node[?], reason: String, rejecting: List[Node[?]] = Nil, subtree: Boolean = false) =
    w.decide(Decisions.Request(n.id, "dev", reason, rejecting.map(_.id), subtree))
  private def acceptAll(w: Workflow): Unit =
    w.kb.ordered.foreach(n => ok(accept(w, n, s"${n.id} is right")))

  test("the snapshot is the tree of the Scala definitions") {
    val j = workflow().annotated
    assertEquals(j("roots").get.arr.flatMap(_.str), Seq("OnlyGood"))
    assertEquals(j("nodes").get.arr.flatMap(_("id").flatMap(_.str)), Seq("OnlyGood", "Listed", "Books", "Pick"))
    val ns = nodes(j)
    assertEquals(ns("OnlyGood")("parent"), Some(Json.JNull))
    assertEquals(ns.view.mapValues(field(_, "kind").get).toMap,
      Map("OnlyGood" -> "root", "Listed" -> "refine", "Books" -> "instantiate", "Pick" -> "contract"))
    assert(field(ns("Listed"), "obligation", "statement").exists(_.contains("spec")))
    assertEquals(field(ns("Listed"), "state"), Some("proposed"))
    assertEquals(ns("Pick")("examples").get.arr.flatMap(_("implementation").flatMap(_.str)), Seq("ok", "ok", "ok"))
    assertEquals(ns("Pick")("examples").get.arr.head("given").get.arr.flatMap(_.str), Seq("minPages = 100"))
    assertEquals(j("params").get.arr.flatMap(p => field(p, "means")).toSet, Set("whether an item is worth picking", "the length readers asked for, from the settings"))
    assertEquals(ns("Pick")("code"), Some(Json.JNull)) // its implementation lives in the model's own file
  }

  test("the tree is decided from the root down, always with a reason") {
    val w = workflow()
    assert(accept(w, listed, "because it is right").left.exists(_.contains("accept OnlyGood first")))
    assert(accept(w, onlyGood, " ").left.exists(_.contains("reason")))
    acceptAll(w)
    assert(w.kb.nodes.forall(w.state(_) == "accepted"))
  }

  test("choosing one proposal rejects its alternatives; they are kept through later decisions") {
    val ws = workspace()
    val alt = onlyGood.refine[(List[Item.T], Int) => List[Item.T]]("Bounded", "At most n good items are picked.", why = "Readers want few books.")(
      abs = pick => pick, spec = pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => good(x))))
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, alt, books, pick), ws)
    ok(accept(w, onlyGood, "it is the idea"))
    ok(accept(w, listed, "Items must come from the shelf.", List(alt)))
    assertEquals((w.state(listed), w.state(alt)), ("accepted", "rejected"))
    assert(w.context(books).contains("Rejected alternative Bounded"))
    assert(accept(w, listed, "books are not alternatives", List(books)).left.exists(_.contains("not an alternative")))
    // the agent removes the rejected node, then rewords Listed; the new decision keeps the alternative
    val reworded = onlyGood.refine[(List[Item.T], Int) => List[Item.T]]("Listed", "Every picked item is in the list and is good.", why = listed.why)(
      abs = pick => pick, spec = pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => l.contains(x) && good(x))))
    val w2 = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, reworded), ws)
    assertEquals(w2.state(reworded), "review")
    val before = nodes(w2.annotated)("Listed")
    assertEquals(before("decision").flatMap(_("content")).flatMap(_("statement")).flatMap(_.str), Some(listed.statement))
    ok(accept(w2, reworded, "The wording is clearer."))
    // the reason it was chosen stays; the change is accepted after it
    assertEquals(field(nodes(w2.annotated)("Listed"), "decision", "reason"), Some("Items must come from the shelf."))
    assertEquals(w2.ledger.alternatives("Listed").map(_._1), List("Bounded"))
    assertEquals(w2.ledger.history("Listed").map(_.action), List("accept", "accept"))
  }

  test("a change to the idea reviews the roots only") {
    val ws = workspace()
    val w = workflow(shelfKb, ws)
    acceptAll(w)
    Files.writeString(ws.root.resolve("IDEA.md"), "# Shelf\n\nPick good items, quickly.\n\n## Not modelled\n\n- Prices.\n")
    assertEquals(w.kb.ordered.map(w.state), List("review", "accepted", "accepted", "accepted"))
    assert(field(nodes(w.annotated)("OnlyGood"), "content", "idea").exists(_.contains("quickly")))
  }

  test("after a change, the developer names the decisions below that it may affect") {
    val ws = workspace()
    val w = workflow(shelfKb, ws)
    acceptAll(w)
    Files.writeString(ws.root.resolve("IDEA.md"), "# Shelf\n\nPick good items, quickly.\n\n## Not modelled\n\n- Prices.\n")
    ok(w.decide(Decisions.Request("OnlyGood", "dev", "Picking must be quick now.", revisit = List("Pick"))))
    assert(w.decide(Decisions.Request("Listed", "dev", "OnlyGood is not below it.", revisit = List("OnlyGood"))).left.exists(_.contains("revisited")))
    assertEquals(w.kb.ordered.map(w.state), List("accepted", "accepted", "accepted", "review"))
    assertEquals(nodes(w.annotated)("Pick")("causes").get.arr.flatMap(_.str), Seq("revisit"))
    ok(accept(w, pick, "Filtering a list is quick enough."))
    assertEquals(w.ledger.history("Pick").map(_.action), List("accept", "revisit", "confirm"))
    assertEquals(field(nodes(w.annotated)("Pick"), "decision", "reason"), Some("Pick is right"))
    assert(w.context(pick).contains("To revisit (dev): OnlyGood changed"))
  }

  test("a proposal can be rejected on its own; a reason takes a few words") {
    val alt = onlyGood.refine[(List[Item.T], Int) => List[Item.T]]("Bounded", "At most n good items are picked.", why = "Readers want few books.")(
      abs = pick => pick, spec = pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => good(x))))
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, alt, books, pick))
    assert(accept(w, onlyGood, "ok").left.exists(_.contains("few words")))
    ok(accept(w, onlyGood, "it is the idea"))
    ok(w.decide(Decisions.Request("Bounded", "dev", "Readers want every good book.", verb = "reject")))
    assertEquals((w.state(alt), w.state(listed)), ("rejected", "proposed"))
    assert(w.decide(Decisions.Request("OnlyGood", "dev", "The root is not a proposal.", verb = "reject")).left.exists(_.contains("only a proposal")))
  }

  test("rejecting a node puts what rests on it up for review, and status fails until it is moved") {
    val alt = onlyGood.refine[(List[Item.T], Int) => List[Item.T]]("Bounded", "At most n good items are picked.", why = "Readers want few books.")(
      abs = pick => pick, spec = pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => good(x))))
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, alt, books, pick))
    List(onlyGood, listed, books, pick).foreach(n => ok(accept(w, n, s"${n.id} is right")))
    ok(accept(w, alt, "Readers want fewer books now.", List(listed)))
    assertEquals(w.state(listed), "rejected")
    assertEquals(nodes(w.annotated)("Books")("causes").get.arr.flatMap(_.str), Seq("above"))
    assert(accept(w, books, "Books still hold here.").left.exists(_.contains("accept Listed first")))
    val (text, settled) = w.status
    assert(!settled)
    assert(text.contains("Listed (refine)  [rejected: remove it from the model"), text)
  }

  test("a decision is refused when the node moved since the developer looked at it") {
    val w = workflow()
    assert(w.decide(Decisions.Request("OnlyGood", "dev", "It is the idea.", seen = "stale")).left.exists(_.contains("changed since")))
    val seen = field(nodes(w.annotated)("OnlyGood"), "version").get
    ok(w.decide(Decisions.Request("OnlyGood", "dev", "It is the idea.", seen = seen)))
  }

  test("the ledger only grows; a merge may interleave both sides' decisions") {
    def d(r: String) = Decision("accept", Json.JNull, "", "dev", r, r)
    val base = Ledger(Map("A" -> List(d("1"))))
    val merged = Ledger(Map("A" -> List(d("1"), d("2a"), d("2b"))))
    assertEquals(Ledger.rewrittenSince(Ledger(Map("A" -> List(d("1"), d("2b")))), merged), Nil)
    assertEquals(Ledger.rewrittenSince(base, merged), Nil)
    assert(Ledger.rewrittenSince(merged, base).nonEmpty)
  }

  test("a subtree is confirmed only below nodes that are accepted") {
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val root2 = Node.root[(List[Item.T], Int) => List[Item.T]]("OnlyGood", "Only good items are ever picked.", onlyGood.why)(
      pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => good(x))))
    val listed2 = root2.refine[(List[Item.T], Int) => List[Item.T]]("Listed", "Picked items come from the list, and are good.", listed.why)(
      abs = pick => pick, spec = pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => l.contains(x) && good(x))))
    val books2 = listed2.instantiate[(List[Book], Int) => List[Book]]("Books", books.statement, books.why)(books.substs*)
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(root2, listed2, books2), ws)
    ok(accept(w, root2, "Clearer with 'ever' added.", subtree = true))
    assertEquals(w.kb.ordered.map(w.state), List("accepted", "review", "review"))
  }

  test("a change to a node's meaning shows below, and is confirmed for a whole subtree at once") {
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val root2 = Node.root[(List[Item.T], Int) => List[Item.T]]("OnlyGood", "Only good items are ever picked.", onlyGood.why)(
      pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => good(x))))
    val listed2 = root2.refine[(List[Item.T], Int) => List[Item.T]]("Listed", listed.statement, listed.why)(
      abs = pick => pick, spec = pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => l.contains(x) && good(x))))
    val books2 = listed2.instantiate[(List[Book], Int) => List[Book]]("Books", books.statement, books.why)(books.substs*)
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(root2, listed2, books2), ws)
    assertEquals(w.kb.ordered.map(w.state), List("review", "review", "review"))
    val ns = nodes(w.annotated)
    assertEquals(ns("OnlyGood")("causes").get.arr.flatMap(_.str), Seq("self"))
    assertEquals(ns("Books")("causes").get.arr.flatMap(_.str), Seq("above"))
    ok(accept(w, root2, "Clearer with 'ever' added."))
    ok(accept(w, listed2, "Unaffected by the rewording.", subtree = true))
    assert(w.kb.nodes.forall(w.state(_) == "accepted"), w.kb.nodes.map(w.state))
    assertEquals(w.ledger.history("Books").map(_.action), List("accept", "confirm"))
    assert(w.context(books2).contains("Accepted by dev: Books is right"))
  }

  test("what is not modelled can change without disturbing decisions") {
    val ws = workspace()
    val w = workflow(shelfKb, ws)
    acceptAll(w)
    Files.writeString(ws.root.resolve("IDEA.md"), "# Shelf\n\nPick good items.\n\n## Not modelled\n\n- Prices.\n- Covers.\n")
    // only the roots are reviewed: what is not modelled narrows nothing below them
    assertEquals(w.kb.ordered.map(w.state), List("review", "accepted", "accepted", "accepted"))
  }

  test("a decided node removed from the model shows until the removal is confirmed") {
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, books), ws)
    assertEquals(w.gone, List("Pick"))
    assert(w.status._1.contains("Pick  [review: gone]"))
    ok(w.decide(Decisions.Request("Pick", "dev", "Picking moved to another service.")))
    assertEquals(w.gone, Nil)
  }

  test("a change to the implementation's code shows on its contract") {
    val ws = workspace()
    val impl = Files.createTempDirectory("impl").resolve("Impl.scala")
    Files.writeString(impl, "class Impl")
    val kb = shelfKb.withImplementation(Implementation("Pick", () => (s: List[Book], n: Int) => s.filter(_.pages >= 100).take(n), List(impl.toString, "Model.scala")))
    val w = workflow(kb, ws)
    acceptAll(w)
    assertEquals(field(nodes(w.annotated)("Pick"), "state"), Some("accepted"))
    Files.writeString(impl, "class Impl // faster")
    assertEquals(nodes(w.annotated)("Pick")("causes").get.arr.flatMap(_.str), Seq("code"))
    assert(w.status._1.contains("review: code"))
    ok(w.decide(Decisions.Request("Pick", "dev", "Same behaviour; examples pass.")))
    assertEquals(field(nodes(w.annotated)("Pick"), "state"), Some("accepted"))
  }

  test("a design decision governs files and has nothing to prove") {
    val ws = workspace()
    Files.writeString(ws.root.resolve("Store.scala"), "object Store")
    val cache = pick.design("Cache", "Shelves are cached in memory.", why = "They change once a day.")("Store.scala")
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, books, pick, cache), ws)
    assertEquals(w.kb.problems, Nil)
    acceptAll(w)
    assertEquals(nodes(w.annotated)("Cache")("link"), Some(Json.JNull))
    Files.writeString(ws.root.resolve("Store.scala"), "object Store // redis")
    assertEquals(nodes(w.annotated)("Cache")("causes").get.arr.flatMap(_.str), Seq("code"))
  }

  test("the ledger is the history; a contract shows what it does not promise") {
    val w = workflow()
    ok(accept(w, onlyGood, "it is the idea"))
    assertEquals(Decisions.history(w.ledger).arr.flatMap(_("node").flatMap(_.str)), Seq("OnlyGood"))
    assertEquals(field(nodes(w.annotated)("OnlyGood"), "decision", "by"), Some("dev"))
    assert(nodes(w.annotated)("Pick")("limits").get.arr.flatMap(_.str).exists(_.contains("empty result")))
    assert(Files.isRegularFile(w.writeSnapshot()))
  }

  test("a change to what a term means reviews the nodes that use it") {
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val good2 = Param[Item.T => Boolean]("good", "whether an item is cheap")
    val onlyGood2 = Node.root[(List[Item.T], Int) => List[Item.T]](onlyGood.id, onlyGood.statement, onlyGood.why)(
      pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => good2(x))))
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood2), ws)
    assertEquals(w.state(onlyGood2), "review")
  }

  test("the ledger is compact on disk, and a rewrite of committed decisions is noticed") {
    val ws = workspace()
    val w = workflow(shelfKb, ws)
    acceptAll(w)
    val committed = w.ledger
    val text = Files.readString(ws.ledgerFile)
    assertEquals(Ledger.fromJson(Json.parse(text)), committed)
    val forged = Ledger(committed.decisions.updated("Listed", committed.history("Listed").map(_.copy(reason = "forged"))))
    assertEquals(Ledger.rewrittenSince(committed, forged), List("Listed: decisions recorded earlier were changed or removed"))
    assertEquals(Ledger.rewrittenSince(committed, committed.add("Pick", committed.history("Pick").head)), Nil)
  }


