package frflow.api

import frflow.ledger.ForAgent
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

  test("the inbox: what the developer decides, in order; what the agent does; the requests") {
    val i = Inbox.of(v)
    // The root's new parts are proven to make it, and nothing it says changed: mechanical.
    assertEquals(i.mechanical.map(_.id), List(id("Root")))
    assertEquals(i.ready.map(_.node.id), List(id("Decide")))
    assertEquals(i.later.map(w => w.node.id -> w.waitsFor), List(id("Expiry") -> Some(id("Root"))))
    assertEquals(i.forAgent, List(ForAgent.Replace(id("Forever"), Sample.by, "sessions must end: a stolen token would work forever")))
    assertEquals((i.open.map(_.id), i.answers.map(_.id)), (List(RequestId("R2")), List(RequestId("R1"))))
    val s = i.overview
    assertEquals((s.accepted, s.review, s.proposed, s.rejected, s.forDeveloper, s.forAgent), (5, 2, 1, 1, 3, 1))
    assertEquals(s.mechanical, 1)
    assert(!s.complete)
  }

  test("a node asked of the agent waits with the agent until the request is answered or the node changes") {
    val asked = Request(RequestId("R3"), Some(id("Decide")), "Say 'them' as 'that user'.", Sample.by, Sample.at, RequestStatus.Open,
      seen = v.node(id("Decide")).map(_.review.version))
    val i = Inbox.of(Sample.view(rs = Sample.requests :+ asked))
    assertEquals(i.withAgent.map(_.id), List(id("Decide")))
    assert(!i.queue.exists(_.node.id == id("Decide")))
    val moved = asked.copy(seen = Some(Version("an older version")))
    assert(Inbox.of(Sample.view(rs = Sample.requests :+ moved)).queue.exists(_.node.id == id("Decide")))
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
