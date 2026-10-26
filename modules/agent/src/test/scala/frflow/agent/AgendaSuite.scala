package frflow.agent

import frflow.agent.conversation.*
import frflow.agent.queue.*
import frflow.agent.request.*
import frflow.ledger.{Annotate, Decide}
import frflow.ledger.Dag.*
import frflow.protocol.*
import io.circe.parser.decode
import io.circe.syntax.*
import java.nio.file.{Files, Path}
import java.time.Instant

/** The agent layer's records and rules: requests, the conversation, IDEA.md's sources, the agent's queue. */
class AgendaSuite extends munit.FunSuite:
  private def ok[A](e: Either[AgentRefusal, A]): A = e.fold(r => throw AssertionError(r.message), identity)
  private val now = Instant.parse("2026-01-01T00:00:00Z")

  test("requests and the conversation read back as written; statuses are words") {
    val r = Request(RequestId("R1"), None, "Say more.", "dev", now, RequestStatus.Open)
    assertEquals(decode[Request](r.asJson.noSpaces), Right(r))
    val c = Conversation(List(Said("A shelf.", now)), List(Question("Q1", "Several books?", "Yes.", now, List(Reply("Yes, three.", now)))))
    assertEquals(decode[Conversation](c.asJson.noSpaces), Right(c))
    assertEquals(RequestStatus.values.map(_.toString).toList, List("open", "answered", "closed"))
    // the examples' requests, as committed, still read
    val examples = Iterator.iterate(Path.of(sys.props("user.dir")).toAbsolutePath)(_.getParent).takeWhile(_ != null)
      .map(_.resolve("examples")).find(Files.isDirectory(_)).get
    assertEquals(decode[List[Request]](Files.readString(examples.resolve("keycloak/.frflow/requests.json"))).map(_.map(_.status)),
      Right(List(RequestStatus.Closed)))
  }

  test("answering a request: the one named, the open one on a node, or a new one from the agent") {
    assertEquals(Requests.answer(Nil, "Nowhere", "text", _ => false, now), Left(AgentRefusal.UnknownRequest("Nowhere")))
    val (asked, q) = Requests.ask(Nil, Some(id("A")), "Say which shelf.", "dev", now)
    val (answered, a1) = ok(Requests.answer(asked, "A", "On the first.", _ => true, now))
    assertEquals((a1.id, a1.status, a1.answer), (q.id, RequestStatus.Answered, Some("On the first.")))
    val (fromAgent, a2) = ok(Requests.answer(answered, "B", "Shelves are now listed.", _ == id("B"), now))
    assertEquals((a2.by, a2.node, fromAgent.size), ("agent", Some(id("B")), 2))
    assert(a2.id != q.id)
    assertEquals(Requests.close(fromAgent, List(q.id, RequestId("R0"))), Left(AgentRefusal.NoRequest(List(RequestId("R0")))))
    assertEquals(ok(Requests.close(fromAgent, List(q.id)))._2.map(_.status), List(RequestStatus.Closed))
    // the version of the node the developer asked about
    assertEquals(Requests.ask(Nil, Some(id("A")), "Say which shelf.", "dev", now, Some(Version("v1")))._2.seen, Some(Version("v1")))
  }

  test("the conversation: words, questions numbered with the answer assumed, replies; a later reply stands") {
    val (c1, _) = ok(Talk.say(Conversation.empty, "A shelf of books readers borrow.", now))
    val (c2, q1) = ok(Talk.ask(c1, "Several books?", "Yes, any number.", now))
    val (c3, q2) = ok(Talk.ask(c2, "Two readers, one book?", "No.", now))
    val (c4, _) = ok(Talk.reply(c3, "q1", "Yes.", now))
    val (c5, again) = ok(Talk.reply(c4, "Q1", "Yes, at most three.", now))
    assertEquals((q1.id, q2.id), ("Q1", "Q2"))
    assertEquals((again.answer, again.replies.size), (Some("Yes, at most three."), 2))
    assertEquals(c5.unanswered.map(_.id), List("Q2"))
    assertEquals(Talk.ask(c5, "Who runs it?", " ", now), Left(AgentRefusal.NoAssumption))
    assertEquals(Talk.reply(c5, "Q7", "Yes.", now), Left(AgentRefusal.UnknownQuestion("Q7")))
    assertEquals(Talk.say(c5, "  ", now), Left(AgentRefusal.NoText))
  }

  test("IDEA.md against its conversation: a section naming a question there is not, an answer changed after acceptance") {
    val idea = "# Toy\n\nA shelf.\nFrom: Q1\n\n## Borrowing\nFrom: Q1, Q3\nA reader borrows a book nobody holds.\n"
    val talk = Conversation(questions = List(Question("Q1", "Several books?", "Yes.", now,
      List(Reply("Yes.", now), Reply("Yes, at most three.", now.plusSeconds(60))))))
    assertEquals(IdeaSources.of(idea), List("" -> List("Q1"), "Borrowing" -> List("Q1", "Q3")))
    val accepted = Decision(Action.Accept, "dev", now.plusSeconds(30), "it says what the shelf is for")
    assertEquals(IdeaSources.warnings(idea, talk, None), List("the section \"Borrowing\" of IDEA.md comes from Q3, which the conversation does not have"))
    assert(IdeaSources.warnings(idea, talk, Some(accepted)).exists(_.startsWith("the answer to Q1 changed after IDEA.md was accepted")))
  }

  test("a rejected node is the agent's to replace, and what rests on it to move") {
    val a2 = node("A2", "Every book asked for is found by its title.", parents = List("R")).copy(replaces = Some(id("A")))
    val all = snap(r, a, b, a2)
    val l = right(Decide(all, acceptAll(shelf), accept("A2", "a title finds a book faster"), "dev", stamp(10)))
    assertEquals(Tasks.of(Annotate(all, l), Nil), List(ForAgent.Replace(id("A"), "dev", "A2 was chosen instead: a title finds a book faster"),
      ForAgent.Move(id("B"), ids("A"))))
  }

  test("a revisit is the agent's until it answers on the node") {
    val l = right(Decide(shelf, acceptAll(shelf), Decide.Revisit(id("A"), "shelves may move now"), "dev", stamp(10)))
    def tasks(answeredAt: Int) =
      val answered = ok(Requests.answer(Nil, "A", "A still holds: a shelf lists its books", _ => true, stamp(answeredAt).at))._1
      Tasks.of(Annotate(shelf, l), answered)
    assertEquals(Tasks.of(Annotate(shelf, l), Nil), List(ForAgent.Revisit(id("A"), "shelves may move now")))
    assertEquals(tasks(answeredAt = 11), Nil)
    // an answer from before the revisit does not answer it
    assertEquals(tasks(answeredAt = 5), List(ForAgent.Revisit(id("A"), "shelves may move now")))
  }
