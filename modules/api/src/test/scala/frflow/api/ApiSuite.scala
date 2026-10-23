package frflow.api

import frflow.protocol.*

class ApiSuite extends munit.FunSuite:
  private val v = Sample.view()
  private def id(s: String) = NodeId(s)
  private val dev = Developer(Sample.by)
  private val at = Deciding.At("2026-01-04T12:00:00Z")

  test("a line diff aligns the lines, and folds a run that did not change") {
    val before = (1 to 8).map(i => s"line $i").mkString("\n")
    val after = before.replace("line 4", "line four")
    assertEquals(LineDiff(before, after), List(
      DiffLine(DiffOp.Folded, "2"), DiffLine(DiffOp.Same, "line 3"), DiffLine(DiffOp.Removed, "line 4"),
      DiffLine(DiffOp.Added, "line four"), DiffLine(DiffOp.Same, "line 5"), DiffLine(DiffOp.Folded, "3")))
    assertEquals(LineDiff("same", "same"), List(DiffLine(DiffOp.Folded, "1")))
  }

  test("what changed since a node was decided: its statement, field by field") {
    val d = Details.diff(v, v.node(id("Decide")).get, None)
    assertEquals(d.causes, List(Cause.Self))
    assertEquals(d.self.map(_.field), List("statement"))
    assertEquals(d.self.head.lines.map(_.op), List(DiffOp.Removed, DiffOp.Added))
    assert(!d.statementStale)
    val root = Details.diff(v, v.node(id("Root")).get, None)
    assertEquals((root.partsAdded, root.partsRemoved), (List(id("Expiry"), id("Forever")), Nil))
  }

  test("the inbox: what the developer decides, in order; what the agent does; the requests") {
    val i = Queue.inbox(v)
    // The root's new parts are proven to make it, and nothing it says changed: mechanical.
    assertEquals(i.mechanical.map(_.id), List(id("Root")))
    assertEquals(i.ready.map(_.node.id), List(id("Decide")))
    assertEquals(i.later.map(w => w.node.id -> w.waitsFor), List(id("Expiry") -> Some(id("Root"))))
    assertEquals(i.forAgent.map(t => t.node -> t.kind), List(id("Forever") -> TaskKind.Rejected))
    assertEquals(i.forAgent.head.reason, "sessions must end: a stolen token would work forever")
    assertEquals((i.open.map(_.id), i.answers.map(_.id)), (List(RequestId("R2")), List(RequestId("R1"))))
    val s = i.summary
    assertEquals((s.accepted, s.review, s.proposed, s.rejected, s.forDeveloper, s.forAgent), (5, 2, 1, 1, 3, 1))
    assertEquals(s.mechanical, 1)
    assert(!s.complete)
  }

  test("a node asked of the agent waits with the agent until the request is answered or the node changes") {
    val asked = Request(RequestId("R3"), Some(id("Decide")), "Say 'them' as 'that user'.", Sample.by, Sample.at, RequestStatus.Open,
      seen = v.node(id("Decide")).map(_.review.version))
    val i = Queue.inbox(Sample.view(rs = Sample.requests :+ asked))
    assertEquals(i.withAgent.map(_.id), List(id("Decide")))
    assert(!i.queue.exists(_.node.id == id("Decide")))
    val moved = asked.copy(seen = Some("an older version"))
    assert(Queue.inbox(Sample.view(rs = Sample.requests :+ moved)).queue.exists(_.node.id == id("Decide")))
  }

  test("the tree: a shared part drawn once, under its first parent, and referred to under the others") {
    val t = Trees.of(v, None).toOption.get
    val root = t.main.head
    assertEquals(root.children.map(_.node.id), List(id("NeedsGrant"), id("LetsIn"), id("Expiry"), id("Forever")))
    assertEquals(root.children.head.children.map(_.node.id), List(id("Decide")))
    assertEquals(root.children(1).seeAlso, List(id("Decide")))
    assertEquals(root.children.head.children.head.alsoUnder, List(id("LetsIn")))
    assertEquals((t.assumptions.map(_.node.id), t.definitions.map(_.node.id)), (List(id("StoreKeeps")), List(id("Identities"))))
    assert(Trees.of(v, Some(id("Nope"))).isLeft)
  }

  test("deciding: accept parents first, all or none; a rejection needs a proposal; a revisit a decided node") {
    val l = Sample.ledgerNow
    val both = Deciding(v, l, Decide.Accept(List(id("Expiry"), id("Root")), "an hour bounds a stolen token"), dev, at)
    assertEquals(both.map(after => Deciding.added(v, l, after).decisions.map(x => x.node -> x.decision.action)),
      Right(List(id("Root") -> Action.Confirm, id("Expiry") -> Action.Accept)))
    assert(Deciding(v, l, Decide.Accept(List(id("Expiry")), "an hour bounds a stolen token"), dev, at).left.exists(_.reason.contains("accept Root first")))
    assert(Deciding(v, l, Decide.Reject(id("Decide"), "no, not like this at all"), dev, at).left.exists(_.reason.contains("only a proposal")))
    assert(Deciding(v, l, Decide.Accept(List(id("Decide")), "x"), dev, at).isLeft)
    val revisit = Deciding(v, l, Decide.Revisit(id("LetsIn"), "the expiry may change what a grant is enough for"), dev, at)
    assertEquals(revisit.map(_.current(id("LetsIn")).map(_.action)), Right(Some(Action.Revisit)))
    assert(Deciding(v, l, Decide.Revisit(id("Expiry"), "it is only a proposal now"), dev, at).isLeft)
    val batch = Deciding(v, l, Decide.Confirm("the new parts are proven to make it"), dev, at)
    assertEquals(batch.map(after => Deciding.added(v, l, after).decisions.map(_.node)), Right(List(id("Root"))))
  }

  test("find: the nodes governing a file, a file no node governs, and what mentions some words") {
    assertEquals(Find(v, "src/main/scala/auth/Store.scala"), Found.Governed("src/main/scala/auth/Store.scala", List(v.node(id("Decide")).get)))
    assertEquals(Find(v, "src/main/scala/auth/Other.scala"), Found.Ungoverned("src/main/scala/auth/Other.scala"))
    Find(v, "stolen token") match
      case Found.Mentions(_, hits) => assertEquals(hits.flatMap(_.id), List(id("Expiry"), id("Forever")))
      case other => fail(s"expected mentions, got $other")
  }
