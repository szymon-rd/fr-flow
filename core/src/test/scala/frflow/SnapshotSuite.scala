package frflow

import frflow.fixtures.*
import java.nio.file.{Files, Path}

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
  private def acceptAll(w: Workflow): Unit =
    w.kb.ordered.foreach(n => ok(w.accept(n, "dev", s"${n.id} is right", Nil)))

  test("the snapshot is the tree of the Scala definitions") {
    val j = workflow().snapshot
    assertEquals(j("roots").get.arr.flatMap(_.str), Seq("OnlyGood"))
    assertEquals(j("nodes").get.arr.flatMap(_("id").flatMap(_.str)), Seq("OnlyGood", "Listed", "Books", "Pick"))
    val ns = nodes(j)
    assertEquals(ns("OnlyGood")("parent"), Some(Json.JNull))
    assertEquals(ns.view.mapValues(field(_, "kind").get).toMap,
      Map("OnlyGood" -> "root", "Listed" -> "refine", "Books" -> "instantiate", "Pick" -> "contract"))
    assert(field(ns("Listed"), "obligation", "statement").exists(_.contains("spec")))
    assertEquals(field(ns("Listed"), "state"), Some("proposed"))
    assertEquals(ns("Pick")("examples").get.arr.flatMap(_("implementation").flatMap(_.str)), Seq("ok", "ok"))
    assertEquals(ns("Pick")("examples").get.arr.head("given").get.arr.flatMap(_.str), Seq("minPages = 100"))
    assertEquals(j("params").get.arr.flatMap(p => field(p, "means")).toSet, Set("whether an item is worth picking", "the length readers asked for, from the settings"))
    assert(field(ns("Pick"), "code", "fingerprint").isDefined)
  }

  test("the tree is decided from the root down, always with a reason") {
    val w = workflow()
    assert(w.accept(listed, "dev", "because", Nil).left.exists(_.contains("decide OnlyGood first")))
    assert(w.accept(onlyGood, "dev", " ", Nil).left.exists(_.contains("reason")))
    acceptAll(w)
    assert(w.kb.nodes.forall(w.decision(_) == "accepted"))
  }

  test("choosing one proposal rejects its alternatives; they are kept through later decisions") {
    val ws = workspace()
    val alt = onlyGood.refine[(List[Item.T], Int) => List[Item.T]]("Bounded", "At most n good items are picked.", why = "Readers want few books.")(
      abs = pick => pick, spec = pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => good(x))))
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, alt, books, pick), ws)
    ok(w.accept(onlyGood, "dev", "the idea", Nil))
    ok(w.accept(listed, "dev", "Items must come from the shelf.", List(alt)))
    assertEquals((w.decision(listed), w.decision(alt)), ("accepted", "rejected"))
    assert(w.context(books).contains("Rejected alternative Bounded"))
    assert(w.accept(listed, "dev", "x", List(books)).left.exists(_.contains("not an alternative")))
    // the agent removes the rejected node, then rewords Listed; the new decision keeps the alternative
    val reworded = onlyGood.refine[(List[Item.T], Int) => List[Item.T]]("Listed", "Every picked item is in the list and is good.", why = listed.why)(
      abs = pick => pick, spec = pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => l.contains(x) && good(x))))
    val w2 = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, reworded), ws)
    assertEquals(w2.decision(reworded), "changed")
    val before = nodes(w2.snapshot)("Listed")
    assertEquals(before("decision").flatMap(_("content")).flatMap(_("statement")).flatMap(_.str), Some(listed.statement))
    ok(w2.accept(reworded, "dev", "Clearer wording.", Nil))
    assertEquals(w2.ledger.rejected("Listed").map(_.id), List("Bounded"))
    assertEquals(w2.ledger.history("Listed").map(_.action), List("accept", "accept"))
  }

  test("a change above shows below, and is confirmed for a whole subtree at once") {
    val ws = workspace()
    val w = workflow(shelfKb, ws)
    acceptAll(w)
    Files.writeString(ws.root.resolve("IDEA.md"), "# Shelf\n\nPick good items, quickly.\n\n## Not modelled\n\n- Prices.\n")
    assertEquals(w.kb.ordered.map(w.decision), List("changed", "parent-changed", "parent-changed", "parent-changed"))
    val root = nodes(w.snapshot)("OnlyGood")
    assert(field(root, "content", "idea").exists(_.contains("quickly")))
    ok(w.accept(onlyGood, "dev", "The idea now asks for speed; the rule is the same.", Nil))
    ok(w.decide(Decisions.Request("confirm", "Listed", "dev", "Unaffected by speed.", subtree = true)))
    assert(w.kb.nodes.forall(w.decision(_) == "accepted"), w.kb.nodes.map(w.decision))
  }

  test("what is not modelled can change without disturbing decisions") {
    val ws = workspace()
    val w = workflow(shelfKb, ws)
    acceptAll(w)
    Files.writeString(ws.root.resolve("IDEA.md"), "# Shelf\n\nPick good items.\n\n## Not modelled\n\n- Prices.\n- Covers.\n")
    assert(w.kb.nodes.forall(w.decision(_) == "accepted"))
  }

  test("a decided node removed from the model shows until the removal is confirmed") {
    val ws = workspace()
    acceptAll(workflow(shelfKb, ws))
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, books), ws)
    assertEquals(w.removed, List("Pick"))
    assert(w.status.contains("Pick  [removed"))
    ok(w.decide(Decisions.Request("remove", "Pick", "dev", "Picking moved to another service.")))
    assertEquals(w.removed, Nil)
  }

  test("a change to the implementation's code shows on its contract") {
    val ws = workspace()
    val impl = Files.createTempFile("impl", ".scala")
    Files.writeString(impl, "class Impl")
    val kb = shelfKb.withImplementation(Implementation("Pick", () => (s: List[Book], n: Int) => s.filter(_.pages >= 100).take(n), List(impl.toString)))
    val w = workflow(kb, ws)
    acceptAll(w)
    assertEquals(field(nodes(w.snapshot)("Pick"), "state"), Some("accepted"))
    Files.writeString(impl, "class Impl // faster")
    assertEquals(nodes(w.snapshot)("Pick")("codeChanged"), Some(Json.JBool(true)))
    ok(w.decide(Decisions.Request("confirm", "Pick", "dev", "Same behaviour; examples pass.")))
    assertEquals(nodes(w.snapshot)("Pick")("codeChanged"), Some(Json.JBool(false)))
  }

  test("a design decision governs files and has nothing to prove") {
    val ws = workspace()
    Files.writeString(ws.root.resolve("Store.scala"), "object Store")
    val cache = pick.design("Cache", "Shelves are cached in memory.", why = "They change once a day.")("Store.scala")
    val w = workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, books, pick, cache), ws)
    assertEquals(w.kb.problems, Nil)
    acceptAll(w)
    assertEquals(field(nodes(w.snapshot)("Cache"), "link", "status"), Some("design"))
    Files.writeString(ws.root.resolve("Store.scala"), "object Store // redis")
    assertEquals(nodes(w.snapshot)("Cache")("codeChanged"), Some(Json.JBool(true)))
  }

  test("actions are appended to the event log") {
    val w = workflow()
    ok(w.accept(onlyGood, "dev", "the idea", Nil))
    w.record("render", "")
    val events = Files.readAllLines(w.ws.eventsFile).toArray.toList.map(l => Json.parse(l.toString))
    assertEquals(events.flatMap(_("action").flatMap(_.str)), List("accept", "render"))
    assertEquals(field(nodes(w.snapshot)("OnlyGood"), "decision", "by"), Some("dev"))
    assert(Files.isRegularFile(w.writeSnapshot()))
  }
