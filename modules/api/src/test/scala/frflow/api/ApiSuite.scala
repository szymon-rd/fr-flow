package frflow.api

import frflow.protocol.*

class ApiSuite extends munit.FunSuite:
  private val v = Sample.view()
  private def id(s: String) = NodeId(s)

  test("a line diff aligns the lines, and folds a run that did not change") {
    val before = (1 to 8).map(i => s"line $i").mkString("\n")
    val after = before.replace("line 4", "line four")
    assertEquals(LineDiff(before, after), List(DiffLine.Folded(2), DiffLine.Same("line 3"), DiffLine.Removed("line 4"),
      DiffLine.Added("line four"), DiffLine.Same("line 5"), DiffLine.Folded(3)))
    assertEquals(LineDiff("same", "same"), List(DiffLine.Folded(1)))
  }

  test("what changed since a node was decided: its statement, field by field") {
    val d = Details.diff(v, v.node(id("Decide")).get, None)
    assertEquals(d.causes, List(Cause.Self))
    assertEquals(d.self.map(_.field), List("statement"))
    assert(d.self.head.lines.map(_.getClass.getSimpleName) == List("Removed", "Added"), d.self.head.lines)
    assert(!d.statementStale)
    val root = Details.diff(v, v.node(id("Root")).get, None)
    assertEquals((root.partsAdded, root.partsRemoved), (List(id("Expiry"), id("Forever")), Nil))
  }

  test("the inbox: what the developer decides, in order") {
    val i = Inbox.of(v)
    // The root's new parts are proven to make it, and nothing it says changed: mechanical.
    assertEquals(i.mechanical.map(_.id), List(id("Root")))
    assertEquals(i.ready.map(_.node.id), List(id("Decide")))
    assertEquals(i.later.map(w => w.node.id -> w.waitsFor), List(id("Expiry") -> Some(id("Root"))))
    val s = i.overview
    assertEquals((s.accepted, s.review, s.proposed, s.rejected, s.forDeveloper), (5, 2, 1, 1, 3))
    assertEquals(s.mechanical, 1)
    assert(!s.complete)
  }

  test("a node a layer on top holds back is aside, not in the queue; a mechanical one stays in the batch") {
    val i = Inbox.of(v, held = Set(id("Decide"), id("Root")))
    assertEquals(i.aside.map(_.id), List(id("Decide")))
    assert(!i.queue.exists(_.node.id == id("Decide")))
    assertEquals(i.mechanical.map(_.id), List(id("Root")))
  }

  test("the tree: a shared part drawn once, under its first parent, and referred to under the others") {
    val t = Trees.all(v)
    val root = t.main.head
    assertEquals(root.children.map(_.node.id), List(id("NeedsGrant"), id("LetsIn"), id("Expiry"), id("Forever")))
    assertEquals(root.children.head.children.map(_.node.id), List(id("Decide")))
    assertEquals(root.children(1).seeAlso, List(id("Decide")))
    assertEquals((t.assumptions.map(_.node.id), t.definitions.map(_.node.id)), (List(id("StoreKeeps")), List(id("Identities"))))
    assertEquals(Trees.from(v, id("Nope")), None)
    // From a node, a part is drawn under a parent among those drawn, not referred to one outside.
    assertEquals(Trees.from(v, id("LetsIn")).map(_.main.head.children.map(_.node.id)), Some(List(id("Decide"))))
  }

  test("check exits 1 on a node proven with an obligation left open: its implementation, or a failing example") {
    val proven = CheckedNode(id("Decide"), CheckStatus.Proven, Nil, Nil, Nil, None, Nil, None)
    assert(proven.ok)
    assert(!proven.copy(notProven = List(ObligationName.Impl)).ok)
    assert(!proven.copy(failing = List(FailingExample("expect", "fails"))).ok)
    assert(!proven.copy(idle = Some("admit doing nothing")).ok)
    assert(!proven.copy(testFailure = Some(TestFailure("(\"t\", Path(\"/a\")) ⇒ None", "returned None", 1, 0, 1))).ok)
    assert(!CheckReport(List(proven, proven.copy(notProven = List(ObligationName.Impl))), v, Overview.of(v)).ok)
  }

  test("a failing case is the contract's change when the contract moved and its code did not") {
    assert(Cause.movedUnderCode(List(Cause.Self)))
    assert(Cause.movedUnderCode(List(Cause.Self, Cause.Above)))
    assert(!Cause.movedUnderCode(List(Cause.Self, Cause.Code)))
    assert(!Cause.movedUnderCode(List(Cause.Code)))
    assert(!Cause.movedUnderCode(Nil))
    val f = TestFailure("held = List()", "returned true, which Decide forbids", 1, 0, 1)
    assertEquals(f.said("Decide", contractChanged = true),
      "the contract changed and its code no longer meets it: held = List(): returned true, which the contract now forbids")
    assertEquals(f.said("Decide", contractChanged = false), "its code fails a generated case: held = List(): returned true, which Decide forbids")
  }

  test("--json: a node checked says whether it is ok, beside how its check ended, and reads back") {
    import io.circe.syntax.*
    val open = CheckedNode(id("Decide"), CheckStatus.Proven, List(ObligationName.Impl), Nil, Nil, None, Nil, None)
    val json = open.asJson
    assertEquals(json.hcursor.get[String]("status"), Right("proven"))
    assertEquals(json.hcursor.get[Boolean]("ok"), Right(false))
    assertEquals(open.copy(notProven = Nil).asJson.hcursor.get[Boolean]("ok"), Right(true))
    assertEquals(json.as[CheckedNode], Right(open))
  }
