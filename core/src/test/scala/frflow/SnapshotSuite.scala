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
  private def accept(w: Workflow, n: Node[?], reason: String, rejecting: List[Node[?]] = Nil, confirm: List[Node[?]] = Nil) =
    w.decide(Decisions.Request(n.id, "dev", reason, rejecting.map(_.id), confirm = confirm.map(_.id)))
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
    // the model's files are where its nodes are written; a model may span several
    assertEquals(shelfKb.modelFiles.map(f => java.nio.file.Paths.get(f).getFileName.toString), List("Fixtures.scala"))
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
    assert(w.decide(Decisions.Request("Listed", "dev", "OnlyGood is not below it.", revisit = List("OnlyGood"))).left.exists(_.contains("not among")))
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
    ok(w.decide(Decisions.Request("Bounded", "dev", "Readers want every good book.", action = "reject")))
    assertEquals((w.state(alt), w.state(listed)), ("rejected", "proposed"))
    assert(w.decide(Decisions.Request("OnlyGood", "dev", "The root is not a proposal.", action = "reject")).left.exists(_.contains("only a proposal")))
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

  test("a node can opt out of Lean: Scala only, decided by reading, examples still run") {
    // `mkString` is outside the Scala the macro translates; an informal node may use any Scala.
    val titled = books.contract[List[Book], Int, List[Book]]("Titled", "Picked books have a title.",
        why = "Titles are free text; not worth a proof.", formal = false)(
      (shelf, n, picked) => picked.forall(b => b.title.mkString.nonEmpty && long(b)))
      .examples(minPages.bind(100))(
        expect(List(Book("Long", 300)), 1, List(Book("Long", 300)), "a titled book"),
        expect(Nil, 1, Nil, "nothing to pick"),
        reject(List(Book("", 300)), 1, List(Book("", 300)), "a book without a title"))
    val kb = KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, books, titled)
    assertEquals(kb.problems, Nil)
    val w = workflow(kb)
    val n = nodes(w.annotated)("Titled")
    assertEquals(field(n, "link", "status"), Some("informal"))
    assertEquals(n("content").flatMap(_("formal")), Some(Json.JBool(false)))
    assertEquals(n("examples").get.arr.flatMap(_("contract").flatMap(_.str)), Seq("ok", "ok", "ok"))
    assert(!w.generate.formal(titled))
    assert(field(n, "content", "sources", "post").exists(_.contains("mkString")), n)
    // what it refers to is still part of what it is decided on
    assert(n("content").flatMap(_("uses")).exists(_.arr.flatMap(_.str).exists(_.startsWith("long = "))), n)
    // below an informal node there is nothing formal to prove against: it is out of Lean too
    val below = titled.contract[List[Book], Int, List[Book]]("Below", "s", "w")((s, n, p) => p.isEmpty)
    assert(!below.formal)
  }

  test("how the implementation is built is part of the contract's content") {
    assertEquals(shelfKb.implementation(pick).map(_.wiring), Some("(shelf, n) => shelf.filter(_.pages >= minPages.value).take(n)"))
    val w = workflow()
    assertEquals(field(nodes(w.annotated)("Pick"), "content", "implementation"), Some("(shelf, n) => shelf.filter(_.pages >= minPages.value).take(n)"))
  }

  test("a decision is refused when the node moved since the developer looked at it") {
    val w = workflow()
    assert(w.decide(Decisions.Request("OnlyGood", "dev", "It is the idea.", seen = "stale")).left.exists(_.contains("changed since")))
    val seen = field(nodes(w.annotated)("OnlyGood"), "version").get
    ok(w.decide(Decisions.Request("OnlyGood", "dev", "It is the idea.", seen = seen)))
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
    ok(accept(w, onlyGood, "it is the idea"))
    val base = w.ledger
    def d(r: String) = Decision("accept", base.history("OnlyGood").head.content, "", "dev", r, r)
    val ours = base.add("OnlyGood", d("on branch one"))
    val theirs = base.add("OnlyGood", d("on branch two"))
    val merged = Ledger(Map("OnlyGood" -> (ours.history("OnlyGood") :+ theirs.history("OnlyGood").last)))
    assert(merged.forked("OnlyGood"))
    assert(!merged.add("OnlyGood", d("decided again after the merge")).forked("OnlyGood"))
  }

  test("the ledger only grows; a merge may interleave both sides' decisions") {
    def d(r: String) = Decision("accept", Json.JNull, "", "dev", r, r)
    val base = Ledger(Map("A" -> List(d("1"))))
    val merged = Ledger(Map("A" -> List(d("1"), d("2a"), d("2b"))))
  }

  test("decisions below are confirmed by name, only below nodes that are accepted") {
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val root2 = Node.root[(List[Item.T], Int) => List[Item.T]]("OnlyGood", "Only good items are ever picked.", onlyGood.why)(
      pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => good(x))))
    val listed2 = root2.refine[(List[Item.T], Int) => List[Item.T]]("Listed", "Picked items come from the list, and are good.", listed.why)(
      abs = pick => pick, spec = pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => l.contains(x) && good(x))))
    val books2 = listed2.instantiate[(List[Book], Int) => List[Book]]("Books", books.statement, books.why)(books.substs*)
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(root2, listed2, books2), ws)
    // Listed changed itself, so it is decided on its own; nothing below it is listed with the root
    assert(accept(w, root2, "Clearer with 'ever' added.", confirm = List(listed2, books2)).left.exists(_.contains("not among")))
    assertEquals(nodes(w.annotated)("OnlyGood")("below").get.arr, Seq())
    ok(accept(w, root2, "Clearer with 'ever' added."))
    assertEquals(w.kb.ordered.map(w.state), List("accepted", "review", "review"))
  }

  test("the definition as written runs past comments between its chained calls, and not into the next one's") {
    val d = workflow().definition(longPick)
    assert(d.startsWith("val longPick = ") && d.contains(".examples(") && d.endsWith("\"never a short one\"))"), d)
  }

  test("a change to a node's meaning shows below, and what still holds is confirmed by name") {
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
    // (written anew here, as other vals: what they say as written changed too)
    assertEquals(ns("Books")("causes").get.arr.flatMap(_.str), Seq("self", "above"))
    assert(field(ns("Books"), "content", "definition").exists(_.startsWith("val books2 = listed2.instantiate")), ns("Books"))
    ok(accept(w, root2, "Clearer with 'ever' added."))
    ok(accept(w, listed2, "Listed still holds under the clearer root."))
    ok(accept(w, books2, "Books still hold under the clearer root."))
    assert(w.kb.nodes.forall(w.state(_) == "accepted"), w.kb.nodes.map(w.state))
    assertEquals(w.ledger.history("Books").map(_.action), List("accept", "accept"))
    assert(w.context(books2).contains("Chosen by dev because: Books is right"))
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

  test("the ledger is compact on disk") {
    val ws = workspace()
    val w = workflow(shelfKb, ws)
    acceptAll(w)
    val committed = w.ledger
    val text = Files.readString(ws.ledgerFile)
    assertEquals(Ledger.fromJson(Json.parse(text)), committed)
  }

  // Lean is not run here: these mark every link as Lean would.
  private def proven(j: Json): Json = Json.JObj(j.obj.map {
    case ("nodes", Json.JArr(ns)) => "nodes" -> Json.JArr(ns.map(n => Json.JObj(n.obj.map {
      case ("link", l) if l != Json.JNull => "link" -> Json.obj("status" -> Json.str("proven"), "detail" -> Json.str("auto"))
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
    val l1 = decide(Ledger.empty, "OnlyGood", "accept", 1).toOption.get
    assert(Decisions.mechanical(snap, l1, ids("OnlyGood")).exists(_.contains("root nodes hold a choice")))
    // a proposal is the developer's choice; so is what the terms mean
    assert(Decisions.mechanical(snap, l1, ids("Listed")).exists(_.contains("only a node under review")))
    assert(Decisions.mechanical(snap, l1, ids("Books")).exists(_.contains("only a node under review")))
    // there is no agent's decision
    assert(decide(l1, "Listed", "settle", 2, "agent").left.exists(_.contains("unknown decision")))
  }

  test("a merged ledger keeps both branches' decisions") {
    val ws = workspace()
    val w = workflow(shelfKb, ws)
    acceptAll(w)
    val base = w.ledger
    val ours = base.add("Pick", base.history("Pick").last.copy(action = "revisit", reason = "ours", at = "2030-01-01T00:00:00Z"))
    val theirs = base.add("Listed", base.history("Listed").last.copy(action = "revisit", reason = "theirs", at = "2030-01-02T00:00:00Z"))
    val merged = Ledger.merge(ours, theirs)
    assertEquals(merged.current("Pick").map(_.reason), Some("ours"))
    assertEquals(merged.current("Listed").map(_.reason), Some("theirs"))
  }


  test("deciding a large tree stays fast: each node's state is computed once") {
    import Json.*
    // 800 nodes, eight children per node, all accepted
    val ns = (0 until 800).map { i =>
      obj("id" -> str(s"N$i"), "kind" -> str(if i == 0 then "root" else "refine"), "parent" -> (if i == 0 then JNull else str(s"N${(i - 1) / 8}")),
        "hash" -> str(Decision.hash(obj("statement" -> str(s"node $i")))), "parentChain" -> str(if i == 0 then "" else s"c${(i - 1) / 8}"),
        "content" -> obj("statement" -> str(s"node $i")), "link" -> JNull)
    }
    val snap = obj("nodes" -> JArr(ns))
    val ledger = ns.foldLeft(Ledger.empty) { (l, n) =>
      val id = n("id").flatMap(_.str).get
      val parent = n("parent").flatMap(_.str).fold("")(p => s"c${p.drop(1)}")
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
    val l1 = decide(snap, Ledger.empty, "OnlyGood", "accept", 1).toOption.get
    val rejected = decide(snap, l1, "Listed", "reject", 2).fold(e => fail(e), identity)
    assertEquals(List("Listed", "Books", "Pick").map(rejected.current(_).map(_.action)), List.fill(3)(Some("reject")))
    // all accepted; then only Listed's why is reworded
    val all = List("Listed", "Books", "Pick").zipWithIndex.foldLeft(l1)((l, x) => decide(snap, l, x._1, "accept", 3 + x._2).fold(e => fail(e), identity))
    val reworded = Json.JObj(snap.obj.map {
      case ("nodes", Json.JArr(ns)) => "nodes" -> Json.JArr(ns.map { n =>
        if n("id").flatMap(_.str).contains("Listed") then
          val c = Json.JObj(n("content").get.obj.map { case ("why", _) => "why" -> Json.str("Reworded, saying the same."); case f => f })
          Json.JObj(n.obj.map { case ("content", _) => "content" -> c; case ("hash", _) => "hash" -> Json.str(Decision.hash(c)); case f => f })
        else n
      })
      case f => f
    })
    assertEquals(Decisions.causes(reworded, all, nodes(reworded)("Listed")), List("self"))
    assert(Decisions.mechanical(reworded, all, nodes(reworded)("Listed")).isDefined)
    assert(Decisions.causes(reworded, all, nodes(reworded)("Books")).isEmpty) // a why does not cascade
  }

  test("a node relying on another concern is reviewed when that concern's meaning changes") {
    val ws = workspace()
    val pickR = pick.relies(nonNegative, "the page counts it reads are never negative")
    acceptAll(workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, books, pickR, nonNegative), ws))
    val nonNeg2 = Node.root[BigInt => BigInt]("NonNegative", "Results are never below zero.", why = nonNegative.why)(f => forall((x: BigInt) => f(x) >= 0))
    val pickR2 = pick.relies(nonNeg2, "the page counts it reads are never negative")
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, books, pickR2, nonNeg2), ws)
    assertEquals(w.state(pickR2), "review")
    val ns = nodes(w.annotated)
    assertEquals(ns("Pick")("causes").get.arr.flatMap(_.str), Seq("above"))
    // accepting the change lists it among the decisions it may affect
    assertEquals(ns("NonNegative")("below").get.arr.find(_("id").flatMap(_.str).contains("Pick")).flatMap(_("kind")).flatMap(_.str), Some("moved"))
    assert(w.context(pickR2).contains("## It relies on"), w.context(pickR2))
    assert(w.context(nonNeg2).contains("Relied on by"), w.context(nonNeg2))
    // a reliance that leads back to the node itself is refused
    lazy val l: Node[(List[Item.T], Int) => List[Item.T]] = onlyGood.refine[(List[Item.T], Int) => List[Item.T]]("L", "s", "w")(
      abs = pick => pick, spec = pick => forall((xs: List[Item.T], n: Int) => pick(xs, n).forall(x => good(x)))).relies(b, "the books are what it lists")
    lazy val b: Node[(List[Book], Int) => List[Book]] = l.instantiate[(List[Book], Int) => List[Book]]("B", "s", "w")(books.substs*)
    val loop = KnowledgeBase("Loop", idea = "IDEA.md")(onlyGood, l, b)
    assert(loop.problems.exists(_.contains("rests on it")), loop.problems)
  }

  test("a rejected proposal is recognised again with its variables renamed") {
    def a(src: String) = Decisions.alpha(Json.str(src))
    assertEquals(a("pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => good(x)))"),
      a("f => forall((xs: List[Item.T], k: Int) => f(xs, k).forall(y  =>  good(y)))"))
    assertNotEquals(a("f => forall((xs: List[Item.T], k: Int) => f(xs, k).forall(y => good(y)))"),
      a("f => forall((xs: List[Item.T], k: Int) => f(xs, k).forall(y => bad(y)))"))
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

  test("what is not modelled may be split by section, each root decided against its own") {
    val ws = workspace()
    Files.writeString(ws.root.resolve("IDEA.md"),
      "# Shelf\n\n## Picking\n\nPick good items.\n\n## Not modelled\n\n- Prices.\n\n### Picking\n\n- Covers.\n\n### Selling\n\n- Taxes.\n")
    val r = Node.root[(List[Item.T], Int) => List[Item.T]]("OnlyGood", onlyGood.statement, onlyGood.why, idea = "Picking")(
      pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => good(x))))
    val nm = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(r), ws).notModelledOf(r)
    assert(nm.contains("Prices") && nm.contains("Covers") && !nm.contains("Taxes"), nm)
  }

  test("with no developer key, status fails whatever the ledger says") {
    val w = workflow()
    acceptAll(w)
    assert(w.integrity.exists(_.startsWith("no developer key")), w.integrity)
    assert(!w.status._2)
  }

  test("a decision below that says when to revisit it is answered by name before the change above is accepted") {
    val ws = workspace()
    val w0 = workflow(shelfKb, ws)
    ok(accept(w0, onlyGood, "it is the idea"))
    ok(accept(w0, listed, "Items come from the list; revisit if items can come from elsewhere."))
    ok(w0.decide(Decisions.Request("Books", "dev", "Books are the items.", held = List("Listed"))))
    ok(w0.decide(Decisions.Request("Pick", "dev", "Picking is per call.", held = List("Listed"))))
    // only the root's why changes: the decisions below stay accepted, and are listed with it
    val root2 = Node.root[(List[Item.T], Int) => List[Item.T]]("OnlyGood", onlyGood.statement, "Picking a bad item is what the idea rules out, whatever the list.")(
      pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => good(x))))
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(root2, listed, books, pick), ws)
    // Listed's reason names when to revisit it: no default
    assert(accept(w, root2, "The why is clearer now.").left.exists(_.contains("Listed")), accept(w, root2, "The why is clearer now."))
    ok(w.decide(Decisions.Request("OnlyGood", "dev", "The why is clearer now.", held = List("Listed"))))
  }

  test("a new node under a decision that says when to revisit it answers it by name") {
    val w = workflow(shelfKb, workspace())
    ok(accept(w, onlyGood, "it is the idea"))
    ok(accept(w, listed, "Items come from the list; revisit if items can come from elsewhere."))
    // Books is new under it: it answers it
    assert(accept(w, books, "Books are the items.").left.exists(_.contains("Listed")))
    ok(w.decide(Decisions.Request("Books", "dev", "Books are the items.", held = List("Listed"))))
    assertEquals(nodes(w.annotated)("Pick")("conditionsAbove").get.arr.flatMap(_.str), Seq("Listed"))
    assert(accept(w, pick, "Picking is per call.").left.exists(_.contains("Listed")))
    ok(w.decide(Decisions.Request("Pick", "dev", "Picking is per call.", held = List("Listed"))))
    assertEquals(w.ledger.current("Pick").get.held, List("Listed"))
  }

  test("a confirmation it cannot apply is refused, with why, not dropped") {
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val root2 = Node.root[(List[Item.T], Int) => List[Item.T]]("OnlyGood", "Only good items are ever picked.", onlyGood.why)(
      pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => good(x))))
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(root2, listed, books, pick), ws)
    val r = w.decide(Decisions.Request("OnlyGood", "dev", "Clearer with 'ever' added.", confirm = List("Books")))
    assert(r.left.exists(_.contains("Books")), r)
    val h = w.decide(Decisions.Request("OnlyGood", "dev", "Clearer with ever added.", held = List("Elsewhere")))
    assert(h.left.exists(_.contains("not among")), h)
    ok(w.decide(Decisions.Request("OnlyGood", "dev", "Clearer with 'ever' added.", held = List("Listed"))))
  }

  test("a renamed node keeps its history, its reasons and the alternatives rejected for it, in one decision") {
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, books, choose).implement(choose)((shelf, n) => shelf.filter(_.pages >= minPages.value).take(n)), ws)
    val gone = w.annotated("gone").get.arr.toList
    assertEquals(gone.map(g => field(g, "id")), List(Some("Pick")))
    assertEquals(gone.head("renamedTo").get.arr.flatMap(_.str), Seq("Choose"))
    assertEquals(w.state(choose), "proposed")
    // only a node that says the same is a rename
    assert(w.decide(Decisions.Request("Books", "dev", "Books is not Pick renamed.", action = "rename", from = "Pick")).isLeft)
    ok(w.decide(Decisions.Request("Choose", "dev", "Choose says what the call does.", action = "rename", from = "Pick")))
    assertEquals(w.state(choose), "accepted")
    assertEquals(w.gone, Nil)
    assertEquals(w.ledger.history("Choose").map(_.action), List("accept", "accept"))
    assert(field(nodes(w.annotated)("Choose"), "reasonNow").exists(r => r.startsWith("Pick is right") && r.contains("renamed from Pick")),
      field(nodes(w.annotated)("Choose"), "reasonNow"))
    assertEquals(Ledger.fromJson(Json.parse(Files.readString(ws.ledgerFile))).history("Choose").map(_.from), List("", "Pick"))
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

  test("what the idea says users can do, not what it forbids") {
    assertEquals(Workflow.capabilities("A user may see a record only if it is theirs. Users can list everything they can see. No user may delete it."),
      List("Users can list everything they can see."))
  }

  test("a reason that says when to revisit it, in the usual words; a statement of fact is not one") {
    for t <- List("Fine until we add a second server.", "If grants move to LDAP, revisit this.", "Revisit if we add exports.",
        "Reconsider once the store is shared.", "It holds as long as one process decides.") do
      assert(Decisions.conditional(t), t)
    for t <- List("A record stays private until its company shares it.", "Accounts are users of a company.", "Revisit later.") do
      assert(!Decisions.conditional(t), t)
  }

  test("a contract of another knowledge base is decided there: read here, with its signed decisions") {
    val shelf = workflow()
    acceptAll(shelf)
    val ws = Workspace(Files.createTempDirectory("reader"), "../lean")
    Files.writeString(ws.root.resolve("IDEA.md"), "# Reader\n\nA user can make a reading list from the shelf.\n")
    val kb = readerKb(shelf.ws.root.toString)
    assertEquals(kb.problems, Nil)
    val w = workflow(kb, ws)
    val ns = nodes(w.annotated)
    assertEquals(field(ns("Pick"), "imported"), Some("Shelf"))
    assertEquals(field(ns("Pick"), "state"), Some("accepted"))
    assert(w.decide(Decisions.Request("Pick", "dev", "it is fine as it is")).left.exists(_.contains("decided in Shelf")))
    ok(accept(w, shortList, "Readers choose from the shelf."))
    ok(accept(w, readingList, "One call keeps to the shelf."))
    // only this project's decisions are written here
    assertEquals(Ledger.load(ws.ledgerFile).decisions.keySet, Set("ShortList", "ReadingList"))
    // a node below another knowledge base's node would be decided in two places
    assert(KnowledgeBase("Reader", idea = "IDEA.md")(again).uses(shelfKb, "../shelf")(pick).problems.exists(_.contains("Shelf decides")))
  }

  test("a concern with an owner is decided by its owner, and waits for them in everyone else's inbox") {
    val w = workflow(ownedKb)
    assert(accept(w, owned, "negative results are meaningless").left.exists(_.contains("ana's to decide")))
    ok(w.decide(Decisions.Request("Owned", "ana", "negative results are meaningless")))
    assert(Decisions.load(w.annotated).contains("ana: 1"))
  }

  test("five developers on five branches: merged in any order, every decision is kept, and a node two branches decided is decided again") {
    val snap = workflow(teamKb).baseSnapshot
    val ids = nodes(snap)
    def decide(l: Ledger, node: String, by: String, reason: String, at: String) =
      Decisions.decide(snap, l, Decisions.Request(node, by, reason), at).fold(e => fail(s"$node: $e"), identity)
    // Branch i: dev i decides their concern. On branch 1, dev0 also decides their root, differently.
    val branches = (0 until 5).toList.map { i =>
      val l = decide(decide(Ledger.empty, s"NonNeg$i", s"dev$i", s"Concern $i is what users asked for.", s"2030-01-0${i + 1}T00:00:00Z"),
        s"Abs$i", s"dev$i", "The absolute value is never negative.", s"2030-01-0${i + 1}T01:00:00Z")
      if i == 1 then decide(l, "NonNeg0", "dev0", "Concern 0, as dev1's branch needs it.", "2030-01-02T02:00:00Z") else l
    }
    // another developer's concern is refused on any branch
    assert(Decisions.decide(snap, Ledger.empty, Decisions.Request("NonNeg2", "dev0", "it looks right to me"), "x").left.exists(_.contains("dev2's to decide")))
    def states(l: Ledger) = ids.view.mapValues(Decisions.state(snap, l, _)).toMap
    val merges = branches.permutations.map(_.reduceLeft(Ledger.merge)).toList
    assertEquals(merges.map(m => m.decisions.view.mapValues(_.map(Ledger.entry).toSet).toMap).distinct.size, 1)
    assertEquals(merges.map(states).distinct.size, 1)
    val merged = merges.head
    assertEquals(merged.decisions.values.map(_.size).sum, 11)
    assertEquals(states(merged)("NonNeg0"), "review") // decided on two branches: decided again
    assertEquals((1 until 5).map(i => states(merged)(s"NonNeg$i")).toSet, Set("accepted"))
    val again = decide(merged, "NonNeg0", "dev0", "Concern 0 is what users asked for, both branches agree.", "2030-01-06T00:00:00Z")
    assertEquals(states(again)("NonNeg0"), "accepted")
  }
