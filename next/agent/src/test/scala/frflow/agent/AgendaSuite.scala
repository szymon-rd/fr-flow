package frflow.agent

import cats.effect.{IO, Resource}
import cats.syntax.all.*
import frflow.agent.conversation.{Conversation, Talk}
import frflow.agent.request.*
import frflow.agent.store.FileStore
import frflow.agent.work.{AgentView, ForAgent}
import frflow.api.Opened
import frflow.cli.Cli
import frflow.core.name.NodeId
import frflow.decision.rules.Command as Decide
import java.nio.file.Files
import java.time.Instant

/** The agent layer's records: requests and the conversation, read back as written; answering a request; and what is
  * the agent's to do, read off the view.
  */
class AgendaSuite extends munit.CatsEffectSuite:
  private val at = Instant.parse("2026-01-03T10:00:00Z")
  private val (nonNegative, sameAbove) = (NodeId("nonNegative"), NodeId("sameAbove"))
  private val temp = ResourceFunFixture(Resource.make(IO.blocking(Files.createTempDirectory("frflow-agent")))(d =>
    IO.blocking(Files.walk(d).sorted(java.util.Comparator.reverseOrder()).forEach(p => Files.delete(p)))))

  temp.test("requests and the conversation read back as written; statuses are words") { d =>
    val (rs, _) = Requests.ask(Nil, Some(nonNegative), "name the number plainly", Asked("ann", at, Some("v1")))
    val talk = Talk.say(Conversation.empty, "a shelf of numbers", at).map(_._1).getOrElse(Conversation.empty)
    for
      requests <- FileStore.make[IO, List[Request]](d.resolve(".frflow/requests.json"), Nil)
      said     <- FileStore.make[IO, Conversation](d.resolve(".frflow/conversation.json"), Conversation.empty)
      _        <- requests.update[Nothing, Unit](_ => Right((rs, ())))
      _        <- said.update[Nothing, Unit](_ => Right((talk, ())))
      again    <- (requests.load, said.load).tupled
      text     <- IO.blocking(Files.readString(d.resolve(".frflow/requests.json")))
    yield
      assertEquals(again, (rs, talk))
      assert(text.contains("\"status\" : \"open\""), text)
  }

  test("answering a request: the one named, the open one on a node, or a new one from the agent") {
    val (one, r1) = Requests.ask(Nil, Some(nonNegative), "name the number plainly", Asked("ann", at, None))
    val reply = Answer("named it", at.plusSeconds(60))
    val byId = Requests.answer(one, r1.id.value, reply, _ => true).map(_._2)
    val byNode = Requests.answer(one, "nonNegative", reply, _ => true).map(_._2)
    val fresh = Requests.answer(one, "sameAbove", reply, _ == sameAbove).map(_._2)
    assertEquals(byId.map(r => (r.id, r.status, r.answer)), Right((r1.id, RequestStatus.Answered, Some(reply))))
    assertEquals(byNode.map(_.id), Right(r1.id))
    assertEquals(fresh.map(r => (r.node, r.asked.by)), Right((Some(sameAbove), "agent")))
    assertEquals(Requests.answer(one, "nope", reply, _ => false), Left(AgentRefusal.UnknownRequest("nope")))
    assertEquals(Requests.close(one, List(RequestId("R0"))), Left(AgentRefusal.NoRequest(List(RequestId("R0")))))
  }

  test("the conversation: words, questions with the answer assumed, replies; a later reply stands; nothing numbered") {
    val c = for
      (c1, _) <- Talk.say(Conversation.empty, "a shelf of numbers", at)
      (c2, q) <- Talk.ask(c1, "Can a number be negative?", "No, never.", at)
      (c3, _) <- Talk.reply(c2, q.id, "No.", at)
      (c4, a) <- Talk.reply(c3, q.id, "No, and zero is fine.", at.plusSeconds(1))
    yield (c4, q, a)
    c match
      case Right((talk, q, a)) =>
        assert(q.id.startsWith("q") && !q.id.matches("q\\d+"), q.id)
        assertEquals(a.answer, Some("No, and zero is fine."))
        assertEquals((talk.said.size, talk.unanswered), (1, Nil))
      case Left(e)            => fail(e.message)
    assertEquals(Talk.ask(Conversation.empty, "Who?", " ", at).map(_._2), Left(AgentRefusal.NoAssumption))
    assertEquals(Talk.reply(Conversation.empty, "q1", "yes", at).map(_._2), Left(AgentRefusal.UnknownQuestion("q1")))
  }

  test("a rejected node is the agent's to replace, as is what its rejection took with it") {
    val reject = Decide.Reject(nonNegative, "a bound says more than a sign here", None)
    for
      api  <- Opened.api(Opened.before)
      _    <- api.deciding.decide(reject, "ann")
      view <- api.reading.view
    yield assertEquals(AgentView(view, Nil, Conversation.empty).forAgent, List(
      ForAgent.Replace(nonNegative, "ann", "a bound says more than a sign here"),
      ForAgent.Replace(sameAbove, "ann", "nonNegative, which it rested on, was rejected: a bound says more than a " +
        "sign here")))
  }

  test("a revisit is the agent's until it answers on the node") {
    val revisit = Decide.Revisit(sameAbove, "the shelf may hold more")
    for
      api    <- Opened.api(Opened.before).flatMap(Cli.accepted)
      _      <- api.deciding.decide(revisit, "ann")
      view   <- api.reading.view
      later   = Instant.now.plusSeconds(60)
      (rs, _) = Requests.ask(Nil, Some(sameAbove), "(from the agent)", Asked("agent", later, None))
      answered = Requests.answer(rs, "sameAbove", Answer("it still holds: the bound is the same", later), _ => true)
                   .map(_._1).getOrElse(Nil)
    yield
      assertEquals(AgentView(view, Nil, Conversation.empty).forAgent,
        List(ForAgent.Revisit(sameAbove, "the shelf may hold more")))
      assertEquals(AgentView(view, answered, Conversation.empty).forAgent, Nil)
  }
