package frflow

import frflow.fixtures.*
import java.nio.file.Files

/** The snapshot `.frflow/kb.json` and the event log, without Lean. */
class SnapshotSuite extends munit.FunSuite:

  private def workflow = Workflow(shelfKb, Workspace(Files.createTempDirectory("frflow"), "../lean"))

  private def nodes(j: Json) = j("nodes").get.arr.map(n => n("id").flatMap(_.str).get -> n).toMap
  private def field(n: Json, path: String*) = path.foldLeft(Option(n))((j, k) => j.flatMap(_(k))).flatMap(_.str)

  test("the snapshot is the tree of the Scala definitions") {
    val j = workflow.snapshot
    assertEquals(j("roots").get.arr.flatMap(_.str), Seq("OnlyGood"))
    assertEquals(j("nodes").get.arr.flatMap(_("id").flatMap(_.str)), Seq("OnlyGood", "Listed", "Books", "Pick"))
    val ns = nodes(j)
    assertEquals(ns("OnlyGood")("parent"), Some(Json.JNull))
    assertEquals(field(ns("Listed"), "parent"), Some("OnlyGood"))
    assertEquals(ns.view.mapValues(field(_, "kind").get).toMap,
      Map("OnlyGood" -> "root", "Listed" -> "refine", "Books" -> "instantiate", "Pick" -> "contract"))
    assert(field(ns("Listed"), "sources", "abs").isDefined)
    assert(field(ns("Listed"), "obligation", "statement").exists(_.contains("spec")))
    assert(field(ns("Pick"), "rootTheorem").exists(_.startsWith("theorem root")))
    assertEquals(ns("Books")("substitutions").get.arr.flatMap(_("name").flatMap(_.str)), Seq("Item", "good"))
    assertEquals(j("params").get.arr.flatMap(_("name").flatMap(_.str)).toSet, Set("good", "minPages"))
  }

  test("links are not checked until a check records them") {
    val ns = nodes(workflow.snapshot)
    assertEquals(ns("OnlyGood")("link"), Some(Json.JNull))
    assertEquals(field(ns("Listed"), "link", "status"), Some("not-checked"))
    assertEquals(field(ns("Listed"), "decision"), Some("proposed"))
    assertEquals(ns("Pick")("examples").get.arr.flatMap(_("implementation").flatMap(_.str)), Seq("ok", "ok"))
  }

  test("decisions: accepting one proposal rejects its alternatives and keeps them") {
    val w = workflow
    val alt = onlyGood.refine[(List[Item.T], Int) => List[Item.T]]("Bounded", "At most n good items are picked.", why = "Readers want few books.")(
      abs = pick => pick, spec = pick => forall((l: List[Item.T], n: Int) => pick(l, n).forall(x => good(x))))
    val w2 = Workflow(KnowledgeBase("Shelf", idea = "IDEA.md")(onlyGood, listed, alt, books, pick), w.ws)
    assertEquals(w2.decision(listed), "proposed")
    w2.accept(listed, "dev", "Items must come from the shelf.", List(alt))
    assertEquals((w2.decision(listed), w2.decision(alt)), ("accepted", "rejected"))
    val n = nodes(w2.snapshot)("Listed")
    assertEquals(field(n, "decided", "note"), Some("Items must come from the shelf."))
    assertEquals(n("decided").flatMap(_("rejected")).get.arr.flatMap(_("id").flatMap(_.str)), Seq("Bounded"))
    assert(w2.context(books).contains("Rejected Bounded"))
    intercept[IllegalArgumentException](w2.accept(listed, "dev", "", List(books)))
  }

  test("actions are appended to the event log") {
    val w = workflow
    w.accept(onlyGood, "dev", "", Nil)
    w.record("render", "")
    val events = Files.readAllLines(w.ws.eventsFile).toArray.toList.map(l => Json.parse(l.toString))
    assertEquals(events.flatMap(_("action").flatMap(_.str)), List("accept", "render"))
    assertEquals(field(nodes(w.snapshot)("OnlyGood"), "decided", "by"), Some("dev"))
    assert(Files.isRegularFile(w.writeSnapshot()))
  }
