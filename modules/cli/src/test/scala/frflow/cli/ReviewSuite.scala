package frflow.cli

import cats.effect.{ExitCode, IO}
import frflow.api.*
import frflow.protocol.*

/** The review and the decision commands on scripted input, over the in-memory API. */
class ReviewSuite extends munit.CatsEffectSuite with Golden:
  private val st = Style(color = false, unicode = false, width = Some(100))

  test("review: the mechanical batch, a request instead of a decision, then the proposal it unblocked") {
    val typed = List("a", "the new parts are proven to make it", "?", "Name the user as 'that user'.", "a", "an hour bounds a stolen token")
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

  test("review needs a terminal") {
    for
      term <- Scripted(Nil, interactive = false)
      code <- FakeApi().flatMap(ReviewSession(_, term, st).run(None))
    yield assertEquals(code, Run.Usage)
  }

  test("a decision without a terminal needs --yes; with it, it is recorded") {
    def reject(yes: Boolean) = Command.Reject(NodeId("Expiry"), Asked(Some("sessions end on sign-out instead"), None, yes))
    for
      api <- FakeApi()
      term <- Scripted(Nil, interactive = false)
      refused <- Run(api, term, st)(reject(yes = false))
      done <- Run(api, term, st)(reject(yes = true))
      out <- term.output
      ledger <- api.ledgerNow
    yield
      assertEquals((refused, done), (Run.Usage, ExitCode.Success))
      assertEquals(ledger.current(NodeId("Expiry")).map(_.action), Some(Action.Reject))
      assert(out.exists(_.contains("pass --yes")), out)
  }

  test("on a terminal a decision shows what it records and asks first") {
    val accept = Command.Accept(List(NodeId("Decide")), Nil, Asked(None, None, yes = false))
    for
      api <- FakeApi()
      term <- Scripted(List("the wording names the user plainly", "y"))
      code <- Run(api, term, st)(accept)
      out <- term.output
    yield
      assertEquals(code, ExitCode.Success)
      golden("accept", out)
  }

  test("a refused decision exits 1 and says why") {
    for
      api <- FakeApi()
      term <- Scripted(Nil, interactive = false)
      code <- Run(api, term, st)(Command.Accept(List(NodeId("Expiry")), Nil, Asked(Some("an hour bounds a stolen token"), None, yes = true)))
      out <- term.output
    yield
      assertEquals(code, Run.Refused)
      assert(out.exists(_.contains("accept Root first")), out)
  }
