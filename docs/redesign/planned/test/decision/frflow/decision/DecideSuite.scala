package frflow.decision

import frflow.core.name.NodeId
import frflow.decision.content.{Chain, Content}
import frflow.decision.ledger.{Action, Authorship, Bound, Decision, Ledger, Reason}
import frflow.decision.review.{Reading, Subjects}
import frflow.decision.rules.{Command, Decide, Refusal}
import java.time.Instant

class DecideSuite extends munit.FunSuite:
  private val by = Authorship("dev", Instant.EPOCH, None)
  private val gone = NodeId("Gone")
  private val accepted =
    Decision.taken(Action.Accept, by, Reason("it was the plan", Nil), Bound(Content.empty, Chain.empty, None))
  private val reading = Reading(Subjects(Nil), Ledger.empty.add(gone, accepted))

  test("a reason of a word or two is refused, whatever the command") {
    assertEquals(Decide(reading, Command.Gone(gone, "ok"), by), Left(Refusal.NoReason))
  }

  test("a gone node's decision is among the decisions added, so it is signed and reported") {
    val after = Decide(reading, Command.Gone(gone, "removed from the model"), by).toOption.get
    assertEquals(Decide.added(reading, reading.ledger, after).map(_._1), List(gone))
  }
