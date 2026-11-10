package frflow.agent

import frflow.agent.request.{Asked, Requests}
import frflow.agent.work.Moved
import frflow.api.fixture.Opened
import frflow.cli.Cli
import frflow.core.name.NodeId
import frflow.decision.rules.Command as Decide
import java.time.Instant

/** What `wait` reports once the developer moves, read off the ledger and the requests (never the model): each node
  * accepted, rejected with why, or sent back to be revisited, and each request asked since; nothing when nothing
  * moved.
  */
class WaitSuite extends munit.CatsEffectSuite:
  private val (nonNegative, sameAbove) = (NodeId("nonNegative"), NodeId("sameAbove"))

  test("a rejection is reported with its reason, and so is what it took with it; nothing moved is nothing") {
    for
      api    <- Opened.api(Opened.before)
      before <- api.reading.decisions
      _      <- api.deciding.decide(Decide.Reject(nonNegative, "a bound says more than a sign here", None), "ann")
      after  <- api.reading.decisions
    yield
      val moved = Moved.between((before, Nil), (after, Nil))
      assert(moved.contains(Moved.Rejected(nonNegative, "ann", "a bound says more than a sign here")), moved)
      assert(moved.exists { case Moved.Rejected(n, _, _) => n == sameAbove; case _ => false }, moved)
      assertEquals(Moved.between((after, Nil), (after, Nil)), Nil)
  }

  test("an acceptance is reported as accepted, by whom") {
    for
      api      <- Opened.api(Opened.before)
      before   <- api.reading.decisions
      accepted <- Cli.accepted(api).flatMap(_.reading.decisions)
    yield
      val moved = Moved.between((before, Nil), (accepted, Nil))
      assert(moved.nonEmpty && moved.forall { case Moved.Accepted(_, by) => by == "ann"; case _ => false }, moved)
  }

  test("a request asked since is reported; one asked before is not") {
    val at = Instant.parse("2026-01-03T10:00:00Z")
    val (one, _) = Requests.ask(Nil, Some(nonNegative), "name the number plainly", Asked("ann", at, None))
    val (two, second) = Requests.ask(one, None, "add a ceiling too", Asked("ann", at.plusSeconds(5), None))
    assertEquals(Moved.between((Map.empty, one), (Map.empty, two)), List(Moved.Asked(second)))
  }
