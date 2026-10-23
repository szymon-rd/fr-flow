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
  private def strs(n: Json, k: String) = n(k).map(_.arr.flatMap(_.str).toList).getOrElse(Nil)
  private def ok(e: Either[String, Unit]): Unit = assert(e.isRight, e)
  private def accept(w: Workflow, n: Node[?], reason: String, rejecting: List[Node[?]] = Nil, confirm: List[Node[?]] = Nil) =
    w.decide(Decisions.Request(n.id, "dev", reason, rejecting.map(_.id), confirm = confirm.map(_.id)))
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
    val j = workflow().annotated
    assertEquals(field(j, "root"), Some("OnlyGood"))
    assertEquals(strs(j, "definitions"), List("Books", "Picking"))
    assertEquals(strs(j, "trusted"), List("Pick"))
    assertEquals(j("nodes").get.arr.flatMap(_("id").flatMap(_.str)), Seq("Books", "Picking", "OnlyGood", "FromList", "OnlyLong", "EveryLong", "Pick"))
    val ns = nodes(j)
    assertEquals(ns.view.mapValues(field(_, "kind").get).toMap,
      Map("OnlyGood" -> "claim", "Books" -> "definition", "Picking" -> "definition", "FromList" -> "claim", "OnlyLong" -> "claim", "EveryLong" -> "claim", "Pick" -> "contract"))
    assertEquals(strs(ns("OnlyGood"), "parents"), Nil)
    assertEquals(strs(ns("OnlyGood"), "parts"), List("FromList", "OnlyLong", "EveryLong"))
    assertEquals(strs(ns("Pick"), "parents"), List("FromList", "OnlyLong", "EveryLong"))
    assertEquals(field(ns("Pick"), "op"), Some("picks"))
    assertEquals(strs(ns("Books"), "defines"), List("Item", "good"))
    assertEquals(strs(ns("OnlyGood"), "uses").sorted, List("Books", "Picking"))
    assertEquals(ns("OnlyGood")("rule"), Some(Json.JBool(false)))
    assertEquals(field(ns("OnlyGood"), "split", "complete", "status"), Some("unchecked"))
    assertEquals(ns("OnlyGood")("split").get("needed").get.arr.flatMap(_("id").flatMap(_.str)), Seq("FromList", "OnlyLong", "EveryLong"))
    assertEquals(ns("Pick")("split"), Some(Json.JNull))
    assertEquals(field(ns("FromList"), "state"), Some("proposed"))
    assertEquals(ns("Pick")("examples").get.arr.flatMap(_("implementation").flatMap(_.str)), Seq("ok", "ok", "ok", "ok"))
    assertEquals(ns("Pick")("examples").get.arr.head("given").get.arr.flatMap(_.str), Seq("minPages = 100"))
    assertEquals(ns("Pick")("code"), Some(Json.JNull)) // its implementation lives in the model's own file
    // the model's files are where its nodes are written; a model may span several
    assertEquals(shelfKb.modelFiles.map(f => java.nio.file.Paths.get(f).getFileName.toString), List("Fixtures.scala"))
    assert(Decisions.tree(j).contains("Pick (contract)  [proposed, unchecked, examples 4/4, code checked by running] (also under OnlyLong, EveryLong)"), Decisions.tree(j))
  }

  test("the DAG is decided from the root down; a part waits for all its parents and the definitions it uses") {
    val w = workflow()
    assert(accept(w, fromList, "because it is right").left.exists(_.contains("accept OnlyGood first")))
    assert(accept(w, onlyGood, "because it is right").left.exists(_.contains("accept Books first")))
    assert(accept(w, books, " ").left.exists(_.contains("reason")))
    List(books, picking, onlyGood, fromList).foreach(n => ok(accept(w, n, s"${n.id} is right")))
    assert(accept(w, pick, "Pick is right").left.exists(_.contains("accept OnlyLong first")))
    List(onlyLong, everyLong, pick).foreach(n => ok(accept(w, n, s"${n.id} is right")))
    assert(w.kb.nodes.forall(w.state(_) == "accepted"))
  }

  test("choosing one proposal rejects the alternatives it replaces; they are kept through later decisions") {
    val ws = workspace()
    val alt = Node.claim("Bounded", "Picked books come from the shelf, at most n of them.", why = "Readers want few books.")(
      forall((l: List[Book], n: Int) => picks(l, n).forall(b => l.contains(b)))).under(onlyGood).replaces(fromList)
    val w = workflow(shelfWith(pick, alt), ws)
    List(books, picking, onlyGood).foreach(n => ok(accept(w, n, s"${n.id} is right")))
    ok(accept(w, fromList, "Books must come from the shelf.", List(alt)))
    assertEquals((w.state(fromList), w.state(alt)), ("accepted", "rejected"))
    assert(w.context(pick).contains("Rejected alternative Bounded"), w.context(pick))
    // parts of one parent are not alternatives: together they make it
    assert(accept(w, onlyLong, "parts are not alternatives", List(everyLong)).left.exists(_.contains("not an alternative")))
    // the agent removes the rejected node, then rewords FromList; the new decision keeps the alternative
    val reworded = Node.claim("FromList", "Every picked book is on the shelf.", why = fromList.why)(
      forall((l: List[Book], n: Int) => picks(l, n).forall(b => l.contains(b)))).under(onlyGood)
    val w2 = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, books, picking, reworded), ws)
    assertEquals(w2.state(reworded), "review")
    ok(accept(w2, reworded, "The wording is clearer."))
    assertEquals(field(nodes(w2.annotated)("FromList"), "decision", "reason"), Some("Books must come from the shelf."))
    assertEquals(w2.ledger.alternatives("FromList").map(_._1), List("Bounded"))
    assertEquals(w2.ledger.history("FromList").map(_.action), List("accept", "accept"))
  }

  test("a change to the idea's lead reviews the root only") {
    val ws = workspace()
    val w = workflow(shelfKb, ws)
    acceptAll(w)
    Files.writeString(ws.root.resolve("IDEA.md"), "# Shelf\n\nPick good items, quickly.\n\n## Not modelled\n\n- Prices.\n")
    assertEquals(w.kb.ordered.map(n => n.id -> w.state(n)).filter(_._2 != "accepted"), List("OnlyGood" -> "review"))
    assert(field(nodes(w.annotated)("OnlyGood"), "content", "idea").exists(_.contains("quickly")))
  }

  test("after a change, the developer names the decisions below that it may affect; a shared part is listed once") {
    val ws = workspace()
    val w = workflow(shelfKb, ws)
    acceptAll(w)
    Files.writeString(ws.root.resolve("IDEA.md"), "# Shelf\n\nPick good items, quickly.\n\n## Not modelled\n\n- Prices.\n")
    assertEquals(nodes(w.annotated)("OnlyGood")("below").get.arr.flatMap(_("id").flatMap(_.str)).count(_ == "Pick"), 1)
    ok(w.decide(Decisions.Request("OnlyGood", "dev", "Picking must be quick now.", revisit = List("Pick"))))
    assert(w.decide(Decisions.Request("FromList", "dev", "OnlyGood is not below it.", revisit = List("OnlyGood"))).left.exists(_.contains("not among")))
    assertEquals(w.kb.ordered.map(n => n.id -> w.state(n)).filter(_._2 != "accepted"), List("Pick" -> "review"))
    assertEquals(nodes(w.annotated)("Pick")("causes").get.arr.flatMap(_.str), Seq("revisit"))
    ok(accept(w, pick, "Filtering a list is quick enough."))
    assertEquals(w.ledger.history("Pick").map(_.action), List("accept", "revisit", "confirm"))
    assertEquals(field(nodes(w.annotated)("Pick"), "decision", "reason"), Some("Pick is right"))
    assert(w.context(pick).contains("To revisit (dev): OnlyGood changed"))
  }

  test("a proposal can be rejected on its own; a reason takes a few words") {
    val alt = Node.claim("Bounded", "Picked books come from the shelf, at most n of them.", why = "Readers want few books.")(
      forall((l: List[Book], n: Int) => picks(l, n).forall(b => l.contains(b)))).under(onlyGood).replaces(fromList)
    val w = workflow(shelfWith(pick, alt))
    assert(accept(w, books, "ok").left.exists(_.contains("few words")))
    List(books, picking, onlyGood).foreach(n => ok(accept(w, n, s"${n.id} is right")))
    ok(w.decide(Decisions.Request("Bounded", "dev", "Readers want every good book.", action = "reject")))
    assertEquals((w.state(alt), w.state(fromList)), ("rejected", "proposed"))
    assert(w.decide(Decisions.Request("OnlyGood", "dev", "The root is not a proposal.", action = "reject")).left.exists(_.contains("only a proposal")))
  }

  test("rejecting a node puts what rests on it up for review, and status fails until it is moved") {
    val alt = Node.claim("Bounded", "Picked books come from the shelf, at most n of them.", why = "Readers want few books.")(
      forall((l: List[Book], n: Int) => picks(l, n).forall(b => l.contains(b)))).under(onlyGood).replaces(fromList)
    val w = workflow(shelfWith(pick, alt))
    shelfKb.ordered.foreach(n => ok(accept(w, n, s"${n.id} is right")))
    ok(accept(w, alt, "Readers want fewer books now.", List(fromList)))
    assertEquals(w.state(fromList), "rejected")
    assertEquals(nodes(w.annotated)("Pick")("causes").get.arr.flatMap(_.str), Seq("above"))
    assert(accept(w, pick, "Pick still holds here.").left.exists(_.contains("accept FromList first")))
    val (text, settled) = w.status
    assert(!settled)
    assert(text.contains("FromList (claim)  [rejected: remove it from the model"), text)
    assert(Decisions.inbox(Some(w.annotated), Nil).contains("Pick: rests on rejected FromList"))
    // The agent reads why: the reason may ask for something in the node's place.
    val inbox = Decisions.inbox(Some(w.annotated), Nil)
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
    assertEquals(field(n, "status"), Some("informal"))
    assertEquals(n("content").flatMap(_("formal")), Some(Json.JBool(false)))
    assertEquals(n("examples").get.arr.flatMap(_("contract").flatMap(_.str)), Seq("ok", "ok", "ok"))
    assert(!w.generate.formal(titled))
    assert(field(n, "content", "sources", "post").exists(_.contains("mkString")), n)
    // what it refers to is still part of what it is decided on
    assert(n("content").flatMap(_("uses")).exists(_.arr.flatMap(_.str).exists(_.startsWith("long = "))), n)
    // its parents' splits are decided by reading: Lean cannot state them
    assertEquals(field(ns("FromList"), "split", "complete", "status"), Some("informal"))
  }

  test("how the implementation is built is part of the contract's content") {
    assertEquals(shelfKb.implementation(pick).map(_.wiring), Some("(shelf, n) => shelf.filter(_.pages >= minPages.value)"))
    val w = workflow()
    assertEquals(field(nodes(w.annotated)("Pick"), "content", "implementation"), Some("(shelf, n) => shelf.filter(_.pages >= minPages.value)"))
  }

  test("a decision is refused when the node moved since the developer looked at it") {
    val w = workflow()
    assert(w.decide(Decisions.Request("Books", "dev", "It is the idea.", seen = "stale")).left.exists(_.contains("changed since")))
    val seen = field(nodes(w.annotated)("Books"), "version").get
    ok(w.decide(Decisions.Request("Books", "dev", "It is the idea.", seen = seen)))
  }

  test("repeated content is written once and survives a merge that interleaves entries") {
    val c1 = Json.obj("statement" -> Json.str("one"))
    val c2 = Json.obj("statement" -> Json.str("two"))
    def d(c: Json, r: String) = Decision("accept", c, "", "dev", r, r)
    val l = Ledger(Map("A" -> List(d(c1, "1"), d(c2, "2"), d(c1, "3"))))
    assert(l.toJson.render().contains("same:"))
    assertEquals(Ledger.fromJson(Json.parse(l.toJson.render())), l)
  }

  test("when two branches decided the same node and both were kept, it is decided again") {
    val w = workflow()
    ok(accept(w, books, "it is the idea"))
    val base = w.ledger
    def d(r: String) = Decision("accept", base.history("Books").head.content, "", "dev", r, r)
    val ours = base.add("Books", d("on branch one"))
    val theirs = base.add("Books", d("on branch two"))
    val merged = Ledger(Map("Books" -> (ours.history("Books") :+ theirs.history("Books").last)))
    assert(merged.forked("Books"))
    assert(!merged.add("Books", d("decided again after the merge")).forked("Books"))
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
    assertEquals(nodes(w.annotated)("OnlyGood")("below").get.arr.flatMap(_("id").flatMap(_.str)), Seq("OnlyLong", "Books", "Picking"))
    ok(accept(w, r2, "Clearer with 'only then' added."))
    assertEquals(w.kb.ordered.map(n => n.id -> w.state(n)).filter(_._2 != "accepted").map(_._1), List("FromList", "OnlyLong", "Pick"))
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
    assertEquals(ns("OnlyGood")("causes").get.arr.flatMap(_.str), Seq("self"))
    assertEquals(ns("FromList")("causes").get.arr.flatMap(_.str), Seq("above"))
    assertEquals(ns("Pick")("causes").get.arr.flatMap(_.str), Seq("above"))
    assertEquals(ns("OnlyGood")("below").get.arr.map(b => b("id").flatMap(_.str).get -> b("kind").flatMap(_.str).get).toList,
      List("FromList" -> "moved", "OnlyLong" -> "moved", "Pick" -> "moved", "Books" -> "accepted", "Picking" -> "accepted")) // parents first
    ok(accept(w, r2, "Clearer with 'only then' added.", confirm = List(now(3), now(4), now(5))))
    assert(w.kb.nodes.forall(w.state(_) == "accepted"), w.kb.nodes.map(w.state))
    assertEquals(w.ledger.history("Pick").map(_.action), List("accept", "confirm"))
    assert(w.context(now(5)).contains("Chosen by dev because: Pick is right"))
  }

  test("a statement reworded, its formula unchanged, reviews that node only; what is below is listed under it, not sent to review") {
    val ws = workspace()
    acceptAll(workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(under(onlyGood)*), ws))
    val now = under(rootReworded)
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(now*), ws)
    assertEquals(w.kb.ordered.map(n => n.id -> w.state(n)).filter(_._2 != "accepted"), List("OnlyGood" -> "review"))
    val ns = nodes(w.annotated)
    assertEquals(ns("OnlyGood")("causes").get.arr.flatMap(_.str), Seq("self"))
    // what may be affected: the decisions below it, each to revisit by name if it is
    assertEquals(ns("OnlyGood")("below").get.arr.map(b => b("id").flatMap(_.str).get -> b("kind").flatMap(_.str).get).toList,
      List("FromList" -> "accepted", "OnlyLong" -> "accepted", "Pick" -> "accepted", "Books" -> "accepted", "Picking" -> "accepted"))
    assertEquals(ns("Pick")("moved").get.arr, Nil)
    ok(accept(w, rootReworded, "Clearer with 'only then' added."))
    assert(w.kb.nodes.forall(w.state(_) == "accepted"), w.kb.nodes.map(w.state))
    // after it, a change of its formula still moves what is below
    val w2 = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(under(root2)*), ws)
    assertEquals(nodes(w2.annotated)("Pick")("causes").get.arr.flatMap(_.str), Seq("above"))
    // a node out of Lean is its words: rewording it moves what is below
    val ws3 = workspace()
    def informal(statement: String) = Node.claim("Informal", statement, why = "w", formal = false)(forall((x: BigInt) => sq(x) >= 0))
    def kb3(statement: String) =
      val top = informal(statement)
      KnowledgeBase("Team", idea = "IDEA.md")(top, Node.claim("Floor", "Results are at least zero.", why = "w")(forall((x: BigInt) => sq(x) >= 0)).under(top))
    acceptAll(workflow(kb3("Results are never negative."), ws3))
    assertEquals(nodes(workflow(kb3("Results are never below zero."), ws3).annotated)("Floor")("causes").get.arr.flatMap(_.str), Seq("above"))
  }

  test("what is not modelled can change without disturbing decisions") {
    val ws = workspace()
    val w = workflow(shelfKb, ws)
    acceptAll(w)
    Files.writeString(ws.root.resolve("IDEA.md"), "# Shelf\n\nPick good items.\n\n## Not modelled\n\n- Prices.\n- Covers.\n")
    // only the root is reviewed: what is not modelled narrows nothing below it
    assertEquals(w.kb.ordered.map(n => n.id -> w.state(n)).filter(_._2 != "accepted"), List("OnlyGood" -> "review"))
  }

  test("a decided node removed from the model shows until the removal is confirmed") {
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(shelfNodes*), ws)
    assertEquals(w.gone, List("Pick"))
    assert(w.status._1.contains("Pick  [review: gone]"))
    ok(w.decide(Decisions.Request("Pick", "dev", "Picking moved to another service.")))
    assertEquals(w.gone, Nil)
  }

  test("a change to the implementation's code shows on its contract") {
    val ws = workspace()
    val impl = Files.createTempDirectory("impl").resolve("Impl.scala")
    Files.writeString(impl, "class Impl")
    val kb = shelfKb.withImplementation(Implementation("Pick", () => (s: List[Book], n: Int) => s.filter(_.pages >= 100), List(impl.toString, "Model.scala")))
    val w = workflow(kb, ws)
    acceptAll(w)
    assertEquals(field(nodes(w.annotated)("Pick"), "state"), Some("accepted"))
    Files.writeString(impl, "class Impl // faster")
    assertEquals(nodes(w.annotated)("Pick")("causes").get.arr.flatMap(_.str), Seq("code"))
    assert(w.status._1.contains("review: code"))
    ok(w.decide(Decisions.Request("Pick", "dev", "Same behaviour; examples pass.")))
    assertEquals(field(nodes(w.annotated)("Pick"), "state"), Some("accepted"))
  }

  test("a design decision governs files, sits under what it serves, and has nothing to prove") {
    val ws = workspace()
    Files.writeString(ws.root.resolve("Store.scala"), "object Store")
    val cache = Node.design("Cache", "Shelves are cached in memory.", why = "They change once a day.")("Store.scala").under(pick)
    val w = workflow(shelfWith(pick, cache), ws)
    assertEquals(w.kb.problems, Nil)
    acceptAll(w)
    assertEquals(nodes(w.annotated)("Cache")("split"), Some(Json.JNull))
    assertEquals(nodes(w.annotated)("Cache")("status"), Some(Json.JNull))
    Files.writeString(ws.root.resolve("Store.scala"), "object Store // redis")
    assertEquals(nodes(w.annotated)("Cache")("causes").get.arr.flatMap(_.str), Seq("code"))
  }

  test("the ledger is the history; a contract shows what it does not promise") {
    val w = workflow(callsKb)
    ok(accept(w, pickedAgain, "it is the idea"))
    assertEquals(Decisions.history(w.ledger).arr.flatMap(_("node").flatMap(_.str)), Seq("PickedAgain"))
    assertEquals(field(nodes(w.annotated)("PickedAgain"), "decision", "by"), Some("dev"))
    assert(nodes(w.annotated)("PickPromise")("limits").get.arr.flatMap(_.str).exists(_.contains("empty result")))
    assert(Files.isRegularFile(w.writeSnapshot()))
  }

  test("a change to what a term means reviews the nodes that use it") {
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val good2 = Param[Item.T => Boolean]("good", "whether an item is cheap")
    val onlyGood2 = Node.claim(onlyGood.id, onlyGood.statement, onlyGood.why)(
      forall((l: List[Item.T], x: Item.T) => shown(l, x) == (l.contains(x) && good2(x))))
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood2, books, picking), ws)
    assertEquals(w.state(onlyGood2), "review")
  }

  test("a change to a definition reviews the nodes that use its terms") {
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val thick = Node.definition("Books", "Items are books; a book is good when it is thick.", why = books.why)(
      Item := of[Book], good := ((b: Book) => b.pages >= 500))
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(((thick :: shelfNodes.filterNot(_ eq books)) :+ pick)*), ws)
    val ns = nodes(w.annotated)
    assertEquals(ns("Books")("causes").get.arr.flatMap(_.str), Seq("self"))
    assertEquals(ns("OnlyGood")("causes").get.arr.flatMap(_.str), Seq("above"))
    // what does not use the term rests on what does: the root, whose meaning moved
    assertEquals(ns("FromList")("causes").get.arr.flatMap(_.str), Seq("above"))
  }

  test("a definition with an alternative: what uses the term waits for the choice, and the choice is in force") {
    val ws = workspace()
    val thick = Node.definition("Thick", "A book is good when it is thick.", why = "Readers want long reads.")(good := ((b: Book) => b.pages >= 500))
    val w = workflow(shelfWith(pick, thick), ws)
    assertEquals(w.generate.undecided, Set("good"))
    assert(nodes(w.annotated)("Thick")("defines").exists(_.arr.flatMap(_.str) == Seq("good")))
    assert(Decisions.alternatives(nodes(w.annotated)("Thick"), nodes(w.annotated)("Books")))
    ok(accept(w, books, "Length is what readers asked for.", List(thick)))
    assertEquals(w.state(thick), "rejected")
    assertEquals(w.generate.undecided, Set.empty[String])
    assertEquals(w.generate.inForce.get("good").map(_.id), Some("Books"))
  }

  test("the ledger is compact on disk") {
    val ws = workspace()
    val w = workflow(shelfKb, ws)
    acceptAll(w)
    val committed = w.ledger
    val text = Files.readString(ws.ledgerFile)
    assertEquals(Ledger.fromJson(Json.parse(text)), committed)
  }

  // Lean is not run here: these mark every node as Lean would.
  private def proven(j: Json): Json = Json.JObj(j.obj.map {
    case ("nodes", Json.JArr(ns)) => "nodes" -> Json.JArr(ns.map(n => Json.JObj(n.obj.map {
      case ("status", s) if s != Json.JNull => "status" -> Json.str("proven")
      case ("split", s) if s != Json.JNull => "split" -> Json.obj("complete" -> Json.obj("status" -> Json.str("proven"), "detail" -> Json.str("auto")),
        "needed" -> Json.JArr(Nil), "clash" -> Json.obj("status" -> Json.str("no-clash"), "detail" -> Json.str("")))
      case f => f
    })))
    case f => f
  })

  test("a decision is mechanical only where Lean proves it again and nothing in it is a choice; the agent decides nothing") {
    val w = workflow()
    val snap = proven(w.baseSnapshot)
    def ids = nodes(snap)
    def at(i: Int) = f"2026-01-01T00:00:$i%02dZ"
    def decide(l: Ledger, id: String, action: String, i: Int, by: String = "dev") =
      Decisions.decide(snap, l, Decisions.Request(id, by, s"$id holds for this reason", action = action), at(i))
    val l1 = List("Books", "Picking", "OnlyGood").zipWithIndex.foldLeft(Ledger.empty)((l, x) => decide(l, x._1, "accept", x._2 + 1).toOption.get)
    assert(Decisions.mechanical(snap, l1, ids("Books")).exists(_.contains("definition nodes hold a choice")))
    // a proposal is the developer's choice
    assert(Decisions.mechanical(snap, l1, ids("FromList")).exists(_.contains("only a node under review")))
    // there is no agent's decision
    assert(decide(l1, "FromList", "settle", 5, "agent").left.exists(_.contains("unknown decision")))
  }

  test("deciding a large tree stays fast: each node's state is computed once") {
    import Json.*
    // 800 nodes, eight children per node, all accepted
    val ns = (0 until 800).map { i =>
      obj("id" -> str(s"N$i"), "kind" -> str("claim"), "parents" -> JArr(if i == 0 then Nil else List(str(s"N${(i - 1) / 8}"))),
        "hash" -> str(Decision.hash(obj("statement" -> str(s"node $i")))), "parentChain" -> str(if i == 0 then "" else s"c${(i - 1) / 8}"),
        "content" -> obj("statement" -> str(s"node $i")), "split" -> JNull)
    }
    val snap = obj("nodes" -> JArr(ns))
    val ledger = ns.foldLeft(Ledger.empty) { (l, n) =>
      val id = n("id").flatMap(_.str).get
      val parent = n("parents").get.arr.headOption.flatMap(_.str).fold("")(p => s"c${p.drop(1)}")
      l.add(id, Decision("accept", n("content").get, parent, "dev", "2026-01-01T00:00:00Z", "it is right"))
    }
    val t = System.nanoTime
    val a = Decisions.annotate(snap, ledger)
    val seconds = (System.nanoTime - t) / 1e9
    assert(a("nodes").get.arr.forall(_("state").flatMap(_.str).contains("accepted")), a("nodes").get.arr.head)
    assert(seconds < 5, s"$seconds s")
  }

  test("rejecting a proposal rejects what rests on it; a reworded why is the theory, not mechanical, and does not cascade") {
    val w = workflow()
    val snap = proven(w.baseSnapshot)
    def at(i: Int) = f"2026-01-01T00:01:$i%02dZ"
    def decide(s: Json, l: Ledger, id: String, action: String, i: Int, by: String = "dev") =
      Decisions.decide(s, l, Decisions.Request(id, by, s"$id holds for this reason", action = action), at(i))
    val l1 = List("Books", "Picking", "OnlyGood").zipWithIndex.foldLeft(Ledger.empty)((l, x) => decide(snap, l, x._1, "accept", x._2 + 1).toOption.get)
    val rejected = decide(snap, l1, "FromList", "reject", 5).fold(e => fail(e), identity)
    assertEquals(List("FromList", "Pick").map(rejected.current(_).map(_.action)), List.fill(2)(Some("reject")))
    // all accepted; then only FromList's why is reworded
    val all = List("FromList", "OnlyLong", "EveryLong", "Pick").zipWithIndex.foldLeft(l1)((l, x) => decide(snap, l, x._1, "accept", 10 + x._2).fold(e => fail(e), identity))
    val reworded = Json.JObj(snap.obj.map {
      case ("nodes", Json.JArr(ns)) => "nodes" -> Json.JArr(ns.map { n =>
        if n("id").flatMap(_.str).contains("FromList") then
          val c = Json.JObj(n("content").get.obj.map { case ("why", _) => "why" -> Json.str("Reworded, saying the same."); case f => f })
          Json.JObj(n.obj.map { case ("content", _) => "content" -> c; case ("hash", _) => "hash" -> Json.str(Decision.hash(c)); case f => f })
        else n
      })
      case f => f
    })
    assertEquals(Decisions.causes(reworded, all, nodes(reworded)("FromList")), List("self"))
    assert(Decisions.mechanical(reworded, all, nodes(reworded)("FromList")).isDefined)
    assert(Decisions.causes(reworded, all, nodes(reworded)("Pick")).isEmpty) // a why does not cascade
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
    assertEquals(ns("Again")("causes").get.arr.flatMap(_.str), Seq("above"))
    assertEquals(strs(ns("Again"), "relies"), List("PickPromise"))
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
    assert(field(nodes(w.annotated)("OnlyLong"), "content", "notModelled").exists(_.contains("Prices")))
    assert(field(nodes(w.annotated)("OnlyLong"), "content", "idea").exists(_.contains("Pick only long books")))
    assert(field(nodes(w.annotated)("OnlyGood"), "content", "idea").exists(i => i.contains("Pick good items") && !i.contains("long books")))
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
    val r = w.decide(Decisions.Request("OnlyGood", "dev", "Clearer with 'only then' added.", confirm = List("Books")))
    assert(r.left.exists(_.contains("Books")), r)
    val h = w.decide(Decisions.Request("OnlyGood", "dev", "Clearer with only then added.", revisit = List("Elsewhere")))
    assert(h.left.exists(_.contains("not among")), h)
    ok(w.decide(Decisions.Request("OnlyGood", "dev", "Clearer with 'only then' added.", revisit = List("FromList"))))
  }

  test("a type change is mechanical where nothing the developer decided changed") {
    val w = workflow()
    acceptAll(w)
    val snap = proven(w.baseSnapshot)
    def withUses(f: Seq[Json] => Seq[Json]) = Json.JObj(snap.obj.map {
      case ("nodes", Json.JArr(ns)) => "nodes" -> Json.JArr(ns.map { n =>
        if field(n, "id").contains("Pick") then
          val c = n("content").get
          val c2 = Json.JObj(c.obj.map { case ("uses", u) => "uses" -> Json.JArr(f(u.arr)); case f => f })
          Json.JObj(n.obj.map { case ("content", _) => "content" -> c2; case ("hash", _) => "hash" -> Json.str(Decision.hash(c2)); case f => f })
        else n })
      case f => f })
    // Book gains a field: only the types Pick uses changed, and how its examples print
    val changed = withUses(_.map(u => if u.str.exists(_.startsWith("case class Book")) then Json.str("case class Book(title: String, pages: Int, author: String)") else u))
    val pickNode = nodes(changed)("Pick")
    assertEquals(Decisions.state(changed, w.ledger, pickNode), "review")
    assertEquals(Decisions.mechanical(changed, w.ledger, pickNode), None)
    // a definition it calls is part of what it says: not mechanical
    val redefined = withUses(_ :+ Json.str("long = (b: Book) => b.pages >= 10"))
    assert(Decisions.mechanical(redefined, w.ledger, nodes(redefined)("Pick")).exists(_.contains("changed")))
  }

  test("alternatives are a node and the one it replaces, or two definitions of one term; parts of one parent are not") {
    val a = Json.parse("""{"id":"A","kind":"claim","parents":["R"],"content":{}}""")
    val b = Json.parse("""{"id":"B","kind":"claim","parents":["R"],"replaces":"A","content":{}}""")
    val c = Json.parse("""{"id":"C","kind":"claim","parents":["R"],"content":{}}""")
    val (d1, d2) = (Json.parse("""{"id":"D1","kind":"definition","parents":[],"defines":["good"],"content":{}}"""),
      Json.parse("""{"id":"D2","kind":"definition","parents":[],"defines":["good","Item"],"content":{}}"""))
    assert(Decisions.alternatives(a, b) && Decisions.alternatives(b, a) && Decisions.alternatives(d1, d2))
    assert(!Decisions.alternatives(a, c) && !Decisions.alternatives(a, d1))
  }

  private def causesOf(w: Workflow, id: String) = nodes(w.annotated)(id)("causes").get.arr.flatMap(_.str).toList
  private def ids(j: Json, k: String) = j(k).get.arr.flatMap(_("id").flatMap(_.str)).toList
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
    assertEquals(w.kb.ordered.map(n => n.id -> w.state(n)).filter(_._2 != "accepted"), List("FromList" -> "review", "Bounded" -> "proposed"))
    assertEquals(field(nodes(w.annotated)("Bounded"), "waitsFor"), Some("FromList"))
    // these parts make it: a confirmation, which keeps the reason it was chosen and binds the parts
    ok(accept(w, fromList, "FromList is still made by its parts."))
    assertEquals(w.ledger.history("FromList").map(_.action), List("accept", "confirm"))
    assertEquals(field(nodes(w.annotated)("FromList"), "decision", "reason"), Some("FromList is right"))
    assertEquals(w.ledger.binding("FromList").get.content("parts").get.arr.flatMap(_.str), Seq("Pick", "Bounded"))
    ok(accept(w, newPart, "A bound helps readers."))
    assertEquals(w.kb.nodes.map(w.state).distinct, List("accepted"))
    // and removed: the parent again
    val back = workflow(shelfKb, ws)
    assertEquals(back.kb.ordered.map(n => n.id -> back.state(n)).filter(_._2 != "accepted"), List("FromList" -> "review"))
    assertEquals(causesOf(back, "FromList"), List("parts"))
    assertEquals(back.gone, List("Bounded"))
  }

  test("a change of parts is mechanical when Lean proves the parts make it, each needed; not otherwise") {
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val w = workflow(shelfAnd(pick, newPart), ws)
    val snap = proven(w.baseSnapshot)
    assertEquals(Decisions.causes(snap, w.ledger, nodes(snap)("FromList")), List("parts"))
    assertEquals(Decisions.mechanical(snap, w.ledger, nodes(snap)("FromList")), None)
    def withSplit(complete: String, needed: String) = Json.JObj(snap.obj.map {
      case ("nodes", Json.JArr(ns)) => "nodes" -> Json.JArr(ns.map(n => if !field(n, "id").contains("FromList") then n else Json.JObj(n.obj.map {
        case ("split", _) => "split" -> Json.obj("complete" -> Json.obj("status" -> Json.str(complete), "detail" -> Json.str("")),
          "needed" -> Json.JArr(List("Pick", "Bounded").map(p => Json.obj("id" -> Json.str(p), "status" -> Json.str(needed), "detail" -> Json.str("")))),
          "clash" -> Json.obj("status" -> Json.str("no-clash"), "detail" -> Json.str("")))
        case f => f })))
      case f => f })
    assertEquals(Decisions.mechanical(withSplit("proven", "needed"), w.ledger, nodes(snap)("FromList")), None)
    // a part not needed (Lean shows the parent without it), or the parts not shown to make it: the developer decides
    assert(Decisions.mechanical(withSplit("proven", "not-needed"), w.ledger, nodes(withSplit("proven", "not-needed"))("FromList")).isDefined)
    assert(Decisions.mechanical(withSplit("open", "needed"), w.ledger, nodes(withSplit("open", "needed"))("FromList")).isDefined)
    // a proposal is never mechanical
    assert(Decisions.mechanical(snap, w.ledger, nodes(snap)("Bounded")).exists(_.contains("proposed")))
  }

  test("a diamond: the node under two parents is reviewed once, listed once after both, and confirmed once") {
    val ws = workspace()
    acceptAll(workflow(kbOf(diamond()), ws))
    val now = diamond("Results are never negative, whatever the input.")
    val w = workflow(kbOf(now), ws)
    assertEquals(List("A", "B", "C", "D").map(causesOf(w, _)), List(List("self"), List("above"), List("above"), List("above")))
    val below = nodes(w.annotated)("A")("below").get.arr.toList
    assertEquals(below.map(b => field(b, "id").get), List("B", "C", "D"))
    // D waits for its parents, which wait for A
    assert(accept(w, now(3), "D still holds.").left.exists(_.contains("accept B first")))
    assert(accept(w, now(2), "C still holds.").left.exists(_.contains("accept A first")))
    ok(accept(w, now(0), "Clearer about every input.", confirm = now.drop(1)))
    assertEquals(w.kb.nodes.map(w.state).distinct, List("accepted"))
    assertEquals(w.ledger.history("D").map(_.action), List("accept", "confirm"))
  }

  test("a proposal waits for all of its parents") {
    val w = workflow(kbOf(diamond()))
    List("A", "B").foreach(id => ok(w.decide(Decisions.Request(id, "dev", s"$id is right"))))
    assertEquals(field(nodes(w.annotated)("D"), "waitsFor"), Some("C"))
    assert(w.decide(Decisions.Request("D", "dev", "D is right")).left.exists(_.contains("accept C first")))
    ok(w.decide(Decisions.Request("C", "dev", "C is right")))
    ok(w.decide(Decisions.Request("D", "dev", "D is right")))
  }

  test("a node placed under a second parent: that parent reviews its parts; the node rests on more, and says the same") {
    val ws = workspace()
    acceptAll(workflow(kbOf(diamond(dUnderC = false)), ws))
    val w = workflow(kbOf(diamond()), ws)
    assertEquals(List("A", "B", "C", "D").map(causesOf(w, _)), List(Nil, Nil, List("parts"), List("above")))
    val snap = proven(w.baseSnapshot)
    // both mechanical: Lean proves C's parts make it, and D says what it said
    assertEquals(List("C", "D").map(id => Decisions.mechanical(snap, w.ledger, nodes(snap)(id))), List(None, None))
  }

  test("a change to a definition lists what rests on it, however far down, each once, to confirm by name") {
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val thick = Node.definition("Books", "Items are books; a book is good when it is thick.", why = books.why)(
      Item := of[Book], good := ((b: Book) => b.pages >= 500))
    val now = (thick :: shelfNodes.filterNot(_ eq books)) :+ pick
    val w = workflow(kbOf(now).implement(pick)((shelf, n) => shelf.filter(_.pages >= minPages.value)), ws)
    assertEquals(ids(nodes(w.annotated)("Books"), "below"), List("OnlyGood", "FromList", "OnlyLong", "EveryLong", "Pick"))
    ok(accept(w, thick, "Readers want thick books now.", confirm = now.filter(n => Set("OnlyGood", "FromList", "OnlyLong", "EveryLong", "Pick")(n.id))))
    assertEquals(w.kb.nodes.map(w.state).distinct, List("accepted"))
  }

  test("the alternatives of each node in the model: what it replaces or is replaced by, other definitions of its terms; never its siblings") {
    val alt = Node.claim("Bounded", "Picked books come from the shelf, at most n of them.", why = "Readers want few books.")(
      forall((l: List[Book], n: Int) => picks(l, n).forall(b => l.contains(b)))).under(onlyGood).replaces(fromList)
    val thick = Node.definition("Thick", "A book is good when it is thick.", why = "Readers want long reads.")(good := ((b: Book) => b.pages >= 500))
    val ns = nodes(workflow(shelfWith(pick, alt, thick)).annotated)
    def rivals(id: String) = strs(ns(id), "rivals")
    assertEquals(List("FromList", "Bounded", "Books", "Thick", "OnlyLong").map(rivals), List(List("Bounded"), List("FromList"), List("Thick"), List("Books"), Nil))
  }

  test("a ledger recorded before parts were part of a node's content loads, and nothing is reviewed for it") {
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val l = Ledger.load(ws.ledgerFile)
    val old = Ledger(l.decisions.view.mapValues(_.map(d => d.copy(content = Json.JObj(d.content.obj.filterNot(_._1 == "parts"))))).toMap)
    Ledger.save(ws.ledgerFile, old)
    val w = workflow(shelfKb, ws)
    assertEquals(w.kb.nodes.map(w.state).distinct, List("accepted"))
    // a decided node gone from the model shows as gone
    val w2 = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(shelfNodes*), ws)
    assertEquals(w2.gone, List("Pick"))
  }

  test("placing a node under another parent changes where it rests, not what it says") {
    import Json.*
    def node(parents: List[String], under: String) =
      val c = obj("kind" -> str("claim"), "parents" -> JArr(parents.map(str)), "parts" -> JArr(Nil), "statement" -> str("The result is a square."),
        "definition" -> str(s"val d = Node.claim(\"D\", \"The result is a square.\", why = \"w\")(f)\n  .under($under)\n  .examples()()"))
      obj("id" -> str("D"), "kind" -> str("claim"), "parents" -> JArr(parents.map(str)), "content" -> c, "hash" -> str(Decision.hash(c)), "parentChain" -> str("p"))
    val before = node(List("B"), "b")
    val ledger = Ledger.empty.add("D", Decision("accept", before("content").get, "p", "dev", "2026-01-01T00:00:00Z", "it is right"))
    val now = node(List("B", "C"), "b, c")
    assertEquals(Decisions.causes(obj("nodes" -> JArr(List(now))), ledger, now), Nil)
    // what it says, changed beside the call that places it: itself
    val reworded = Json.JObj(now.obj.map { case ("content", c) => "content" -> Json.JObj(c.obj.map {
      case ("definition", JStr(d)) => "definition" -> str(d.replace(".examples()()", ".examples()(expect(1))")); case f => f })
      case ("hash", _) => "hash" -> str("rehashed below"); case f => f })
    val fixed = Json.JObj(reworded.obj.map { case ("hash", _) => "hash" -> str(Decision.hash(reworded("content").get)); case f => f })
    assertEquals(Decisions.causes(obj("nodes" -> JArr(List(fixed))), ledger, fixed), List("self"))
  }

  test("the code a decision saw, diffed: a file git does not track is compared as it is, not shown as deleted") {
    val repo = Files.createTempDirectory("frflow-git")
    def git(args: String*) =
      val p = ProcessBuilder(("git" +: args)*).directory(repo.toFile).redirectErrorStream(true).start()
      p.getInputStream.readAllBytes(); assertEquals(p.waitFor(), 0, args)
    git("init", "-q"); git("config", "user.email", "t@example.com"); git("config", "user.name", "t")
    val dir = Files.createDirectories(repo.resolve("project"))
    Files.writeString(repo.resolve("README"), "x\n")
    git("add", "README"); git("commit", "-q", "-m", "first")
    // Untracked: the project's files, before its first commit.
    Files.writeString(dir.resolve("Desk.scala"), "val desk = 1\n")
    val tree = Git.snapshot(dir, List("Desk.scala", "New.scala"))
    assert(tree.nonEmpty)
    Files.writeString(dir.resolve("Desk.scala"), "val desk = 1\nval members = 2\n")
    Files.writeString(dir.resolve("New.scala"), "val added = 3\n")
    val d = Git.diff(dir, tree, List("Desk.scala", "New.scala"))
    assert(!d.contains("deleted file"), d)
    assert(d.contains("+val members = 2") && !d.contains("-val desk = 1"), d)
    assert(d.contains("new file") && d.contains("+val added = 3"), d)
    // Removed from the working tree: shown as deleted.
    Files.delete(dir.resolve("Desk.scala"))
    assert(Git.diff(dir, tree, List("Desk.scala")).contains("-val desk = 1"))
    // Nothing changed: no diff; and the repository's own index is untouched.
    Files.writeString(dir.resolve("Desk.scala"), "val desk = 1\n")
    assertEquals(Git.diff(dir, tree, List("Desk.scala")), "")
    assert(!Git.tracked(dir, "Desk.scala"))
  }
