package frflow.cli

import cats.effect.{ExitCode, IO}
import frflow.api.*
import frflow.protocol.*

/** The review and the decision commands on scripted input, over the in-memory API. */
class ReviewSuite extends munit.CatsEffectSuite with Golden:
  private val st = Style(color = false, unicode = false, width = Some(100))

  test("review: the mechanical batch, a request instead of a decision, then the proposal it unblocked") {
    val typed = List("a", "the new parts are proven to make it", "v", "?", "Name the user as 'that user'.", "a", "an hour bounds a stolen token", "y")
    for
      api <- FakeApi()
      term <- Scripted(typed)
      code <- ReviewSession(api, term, st).run(None)
      out <- term.output
      ledger <- api.ledgerNow
      asked <- api.view.map(_.requests.last)
    yield
      assertEquals(code, ExitCode.Success)
      golden("review", out)
      assertEquals(ledger.current(NodeId("Root")).map(_.action), Some(Action.Confirm))
      assertEquals(ledger.current(NodeId("Expiry")).map(d => d.action -> d.reason), Some(Action.Accept -> "an hour bounds a stolen token"))
      assertEquals((asked.node, asked.text), (Some(NodeId("Decide")), "Name the user as 'that user'."))
  }

  test("without a terminal: review is refused, and a decision needs --yes; with it, it is recorded") {
    def reject(yes: Boolean) = Command.Decision(Decide.Reject(NodeId("Expiry"), _), Asked(Some("sessions end on sign-out instead"), None, yes))
    for
      api <- FakeApi()
      term <- Scripted(Nil, interactive = false)
      review <- ReviewSession(api, term, st).run(None)
      refused <- Dispatch(api, term, st)(reject(yes = false))
      done <- Dispatch(api, term, st)(reject(yes = true))
      out <- term.output
      ledger <- api.ledgerNow
    yield
      assertEquals((review, refused, done), (Dispatch.Usage, Dispatch.Usage, ExitCode.Success))
      assertEquals(ledger.current(NodeId("Expiry")).map(_.action), Some(Action.Reject))
      assert(out.exists(_.contains("pass --yes")), out)
  }

  test("on a terminal a decision shows what it records and asks first") {
    val accept = Command.Decision(Decide.Accept(List(NodeId("Decide")), _), Asked(None, None, yes = false))
    for
      api <- FakeApi()
      term <- Scripted(List("the wording names the user plainly", "y"))
      code <- Dispatch(api, term, st)(accept)
      out <- term.output
    yield
      assertEquals(code, ExitCode.Success)
      golden("accept", out)
  }

  test("a refused decision exits 1 and says why") {
    for
      api <- FakeApi()
      term <- Scripted(Nil, interactive = false)
      code <- Dispatch(api, term, st)(Command.Decision(Decide.Accept(List(NodeId("Expiry")), _), Asked(Some("an hour bounds a stolen token"), None, yes = true)))
      out <- term.output
    yield
      assertEquals(code, Dispatch.Refused)
      assert(out.exists(_.contains("accept Root first")), out)
  }

  /** Root's formula changed, so what rests on it moved with it (and Decide reworded, if `reworded`). */
  private def rootMoved(reworded: Boolean = false): Snapshot =
    def changed(n: SnapNode, field: String, to: io.circe.Json) =
      val c = n.content.mapFields { case (`field`, _) => field -> to }
      n.copy(content = c, hash = c.hash)
    val formula = "forall((u, r) => access(u, r) == (authorized(u, r) && signedIn(u)))"
    val root = changed(Sample.root, "sources", io.circe.Json.obj("formula" -> io.circe.Json.fromString(formula)))
    Sample.decided.copy(nodes = Sample.decided.nodes.map(n =>
      if n.id == root.id then root else if reworded && n.id == Sample.decide.id then Sample.reworded.copy(hash = Sample.reworded.content.hash) else n))

  private def review(api: FakeApi, typed: List[String]) =
    Scripted(typed).flatMap(term => ReviewSession(api, term, st).run(None).flatMap(code => term.output.map(code -> _)))

  test("a node waiting for another offers no [a]ccept, and says once what it waits for") {
    (for
      api <- FakeApi()
      (code, out) <- review(api, List("s", "s", "a", "r", "q"))
      ledger <- api.ledgerNow
    yield
      assertEquals(code, ExitCode.Success)
      assert(out.contains("\n[s]kip [v]iew [q]uit [?]ask: a"), out.mkString("\n"))
      assertEquals(out.count(_ == "one of: ? q s v"), 2, out.mkString("\n"))
      assertEquals(out.count(_.contains("Root first")), 1, out.mkString("\n"))
      assert(!out.exists(_.contains("waits for Root")), out.mkString("\n"))
      assertEquals(ledger.current(NodeId("Expiry")), None)) *>
    FakeApi(rootMoved(reworded = true), Sample.ledger, Nil).flatMap(api => review(api, List("s", "a", "q"))).map { (_, out) =>
      // Under review, waiting for what it rests on: one line says so.
      assert(out.contains("  decide NeedsGrant first: what rests on it is decided after it"), out.mkString("\n"))
      assert(!out.exists(_.contains("waits for NeedsGrant")), out.mkString("\n"))
      assertEquals(out.count(_ == "one of: ? q s v"), 1, out.mkString("\n"))
    }
  }

  test("a mistyped name at the revisit prompt is asked again: the reason and the node are kept") {
    val typed = List("a", "the new parts are proven to make it", "a", "Nope", "Memory", "the wording names the user plainly", "y", "q")
    for
      api <- FakeApi()
      (_, out) <- review(api, typed)
      ledger <- api.ledgerNow
    yield
      assert(out.contains("not a decision below Decide: Nope"), out.mkString("\n"))
      assertEquals(out.count(_.startsWith("Revisit any decision below")), 2, out.mkString("\n"))
      assertEquals(ledger.current(NodeId("Decide")).map(d => d.action -> d.reason), Some(Action.Accept -> "the wording names the user plainly"))
      assertEquals(ledger.current(NodeId("Memory")).map(_.action), Some(Action.Revisit))
  }

  test("what moved only with a node: the inbox and the review say the same, and accepting the node confirms it") {
    val followers = List("NeedsGrant", "LetsIn", "Decide")
    for
      api <- FakeApi(rootMoved(), Sample.ledger, Nil)
      inbox <- api.reviewing.map((v, i) => InboxText.lines(i, v, st))
      (_, out) <- review(api, List("a", "", "the formula says the same, in another order", "y"))
      ledger <- api.ledgerNow
    yield
      val said = followers.map(f => s"-> $f moved only with it: accepting Root confirms it too")
      assertEquals(said.map(l => inbox.count(_.trim == l)), List(1, 1, 1), inbox.mkString("\n"))
      assertEquals(said.map(l => out.count(_.trim == l)), List(1, 1, 1), out.mkString("\n"))
      assertEquals(followers.map(f => ledger.current(NodeId(f)).map(_.action)), List.fill(3)(Some(Action.Confirm)))
  }
