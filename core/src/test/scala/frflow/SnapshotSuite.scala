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
    assertEquals(Ledger.rewrittenSince(Ledger(Map("A" -> List(d("1"), d("2b")))), merged), Nil)
    assertEquals(Ledger.rewrittenSince(base, merged), Nil)
    assert(Ledger.rewrittenSince(merged, base).nonEmpty)
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
    assertEquals(Decisions.mechanical(snap, l1, ids("Listed")), None)
    // what the terms mean is a choice, however mechanical it looks
    assert(Decisions.mechanical(snap, l1, ids("Books")).exists(_.contains("instantiate nodes hold a choice")))
    val a1 = Decisions.annotate(snap, l1)
    assertEquals(nodes(a1)("Listed")("mechanical"), Some(Json.JBool(true)))
    assert(Decisions.waiting(a1)._1.contains("Listed: proposed, mechanical"), Decisions.waiting(a1))
    // there is no agent's decision
    assert(decide(l1, "Listed", "settle", 2, "agent").left.exists(_.contains("unknown decision")))
    // a node the developer rejected once is theirs to decide again
    val l4 = decide(l1, "Listed", "reject", 5).fold(e => fail(e), identity)
    assert(Decisions.mechanical(snap, l4, ids("Listed")).isDefined)
    // a link that is not proven is not mechanical
    assert(Decisions.mechanical(w.baseSnapshot, l1, nodes(w.baseSnapshot)("Listed")).exists(_.contains("only a link Lean proves")))
  }

  test("a merged ledger keeps both branches' decisions, and git's full history notices a merge that drops one side") {
    val ws = workspace()
    val w = workflow(shelfKb, ws)
    acceptAll(w)
    val base = w.ledger
    val ours = base.add("Pick", base.history("Pick").last.copy(action = "revisit", reason = "ours", at = "2030-01-01T00:00:00Z"))
    val theirs = base.add("Listed", base.history("Listed").last.copy(action = "revisit", reason = "theirs", at = "2030-01-02T00:00:00Z"))
    val merged = Ledger.merge(ours, theirs)
    assertEquals(Ledger.rewrittenSince(ours, merged), Nil)
    assertEquals(Ledger.rewrittenSince(theirs, merged), Nil)
    assertEquals(merged.current("Pick").map(_.reason), Some("ours"))
    assertEquals(merged.current("Listed").map(_.reason), Some("theirs"))
    // in git: a merge that keeps only one side's ledger (`-s ours`) is a rewrite of the other's
    def git(args: String*) =
      val p = ProcessBuilder(("git" +: args)*).directory(ws.root.toFile).redirectErrorStream(true).start()
      val out = String(p.getInputStream.readAllBytes()); assert(p.waitFor() == 0, out)
    git("init", "-q", "-b", "main"); git("config", "user.email", "t@t"); git("config", "user.name", "t")
    Ledger.save(ws.ledgerFile, base); git("add", "-A"); git("commit", "-qm", "base")
    git("checkout", "-qb", "side"); Ledger.save(ws.ledgerFile, theirs); git("commit", "-qam", "side decides")
    git("checkout", "-q", "main"); git("merge", "-q", "-s", "ours", "side", "-m", "drop side")
    assert(Ledger.rewrites(ws.root, ws.ledgerFile, base).nonEmpty)
  }


  test("deciding a large tree stays fast: each node's state is computed once") {
    import Json.*
    // 800 nodes, eight children per node, all accepted
    val ns = (0 until 800).map { i =>
      obj("id" -> str(s"N$i"), "kind" -> str(if i == 0 then "root" else "refine"), "parent" -> (if i == 0 then JNull else str(s"N${(i - 1) / 8}")),
        "hash" -> str(Decision.hash(obj("statement" -> str(s"node $i")))), "chain" -> str(s"c$i"),
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
    ok(accept(w0, books, "Books are the items."))
    ok(accept(w0, pick, "Picking is per call."))
    // only the root's why changes: the decisions below stay accepted, and are listed with it
    val root2 = Node.root[(List[Item.T], Int) => List[Item.T]]("OnlyGood", onlyGood.statement, "Picking a bad item is what the idea rules out, whatever the list.")(
      pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => good(x))))
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(root2, listed, books, pick), ws)
    // Listed's reason names when to revisit it: no default
    assert(accept(w, root2, "The why is clearer now.").left.exists(_.contains("Listed")), accept(w, root2, "The why is clearer now."))
    ok(w.decide(Decisions.Request("OnlyGood", "dev", "The why is clearer now.", held = List("Listed"))))
  }

  test("a decision copied into the ledger again, or one whose predecessors were cut, shows") {
    val w = workflow()
    acceptAll(w)
    val l = w.ledger
    val first = l.history("Listed").head
    val replayed = l.copy(decisions = l.decisions.updated("Listed", l.history("Listed") :+ first))
    assert(Ledger.chainBreaks(replayed).exists(_.contains("recorded twice")), Ledger.chainBreaks(replayed))
    val l2 = w.decide(Decisions.Request("OnlyGood", "dev", "Reworded reason for the root.", action = "accept")).fold(_ => l, _ => w.ledger)
    assert(Ledger.chainBreaks(w.ledger).isEmpty, Ledger.chainBreaks(w.ledger))
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
    assertEquals(Ledger.chainBreaks(w.ledger), Nil)
    assertEquals(Ledger.fromJson(Json.parse(Files.readString(ws.ledgerFile))).history("Choose").map(_.from), List("", "Pick"))
  }

  test("an idea change nothing follows up is a warning, until a node of its concern is accepted or Not modelled changes") {
    val ws = workspace()
    val w = workflow(shelfKb, ws)
    acceptAll(w)
    assertEquals(w.ideaFollowUps, Nil)
    Files.writeString(ws.root.resolve("IDEA.md"), "# Shelf\n\nPick good items.\n\nA picked item is never damaged.\n\n## Not modelled\n\n- Prices.\n")
    ok(accept(w, onlyGood, "The idea now says a picked item is never damaged."))
    assert(w.ideaFollowUps.exists(_.contains("never damaged")), w.ideaFollowUps)
    assert(w.codeWarnings.exists(_.contains("nothing follows it up")))
    Files.writeString(ws.root.resolve("IDEA.md"), "# Shelf\n\nPick good items.\n\nA picked item is never damaged.\n\n## Not modelled\n\n- Prices.\n- Damage: checked by hand.\n")
    ok(accept(w, onlyGood, "Damage is checked by hand: not modelled."))
    assertEquals(w.ideaFollowUps, Nil)
  }

  test("a type change is not mechanical where the node's words name the type that changed") {
    val w = workflow()
    acceptAll(w)
    val snap = proven(w.baseSnapshot)
    // Book gains a field: Pick says "books", so a reader checks the words still hold
    val changed = Json.JObj(snap.obj.map {
      case ("nodes", Json.JArr(ns)) => "nodes" -> Json.JArr(ns.map { n =>
        if field(n, "id").contains("Pick") then
          val c = n("content").get
          val uses = c("uses").get.arr.map(u => if u.str.exists(_.startsWith("case class Book")) then Json.str("case class Book(title: String, pages: Int, author: String)") else u)
          val c2 = Json.JObj(c.obj.map { case ("uses", _) => "uses" -> Json.JArr(uses); case f => f })
          Json.JObj(n.obj.map { case ("content", _) => "content" -> c2; case ("hash", _) => "hash" -> Json.str(Decision.hash(c2)); case f => f })
        else n })
      case f => f })
    val pickNode = nodes(changed)("Pick")
    assertEquals(Decisions.state(changed, w.ledger, pickNode), "review")
    assert(Decisions.mechanical(changed, w.ledger, pickNode).exists(_.contains("words name book")), Decisions.mechanical(changed, w.ledger, pickNode))
  }

  test("calls varied from the examples keep each value's type, are new, and are the same each time") {
    val vs = Variations.of(pick.cases, 20)
    assert(vs.size >= 10, vs)
    def key(v: Variations.Call) = (v.a, v.b, v.bindings.map(_.value()))
    assertEquals(vs.map(key), Variations.of(pick.cases, 20).map(key))
    vs.foreach { v =>
      assert(v.a.asInstanceOf[List[Any]].forall(_.isInstanceOf[Book]), v.a)
      assert(v.b.isInstanceOf[Int])
      assert(v.bindings.map(_.value()).forall(_.isInstanceOf[Int]))
    }
    val known = pick.cases.map(e => (e.a, e.b, e.bindings.map(_.value()))).toSet
    assert(vs.map(key).forall(!known(_)))
    // an implementation wrong only on a shelf longer than any example's is caught on a varied call
    val wrong = KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, books, pick)
      .implement(pick)((shelf, n) => if shelf.size > 2 then shelf else shelf.filter(_.pages >= minPages.value).take(n))
    assert(wrong.generated(pick).exists(_.example.note.startsWith("varied from example")), wrong.generated(pick))
    assertEquals(shelfKb.generated(pick), Nil)
  }

  test("a decision may say when to revisit it, and a change may restate why the node holds now") {
    val ws = workspace()
    val w0 = workflow(shelfKb, ws)
    ok(accept(w0, onlyGood, "it is the idea"))
    ok(w0.decide(Decisions.Request("Listed", "dev", "Items come from the list offered.", revisitIf = "items can come from elsewhere")))
    ok(accept(w0, books, "Books are the items."))
    ok(accept(w0, pick, "Picking is per call."))
    assertEquals(field(nodes(w0.annotated)("Listed"), "revisitIf"), Some("items can come from elsewhere"))
    // the root's why changes: Listed names when to revisit it, in its field, so it is answered by name
    val root2 = Node.root[(List[Item.T], Int) => List[Item.T]]("OnlyGood", onlyGood.statement, "Picking a bad item is what the idea rules out, whatever the list.")(
      pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => good(x))))
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(root2, listed, books, pick), ws)
    assert(accept(w, root2, "The why is clearer now.").left.exists(_.contains("Listed")))
    ok(w.decide(Decisions.Request("OnlyGood", "dev", "The why is clearer now.", held = List("Listed"),
      standing = "Picking only good items is the idea, whatever the list.")))
    assertEquals(field(nodes(w.annotated)("OnlyGood"), "standing"), Some("Picking only good items is the idea, whatever the list."))
    assert(field(nodes(w.annotated)("OnlyGood"), "reasonNow").exists(_.startsWith("Picking only good items")))
    assert(w.context(listed).contains("Revisit if: items can come from elsewhere"))
    assertEquals(Signing.payload("Listed", w.ledger.history("Listed").head).length > 0, true)
  }

  test("the model's @main only runs the CLI") {
    val w = workflow()
    assert(!w.modelCode.exists(_.contains("@main")), w.modelCode)
  }
