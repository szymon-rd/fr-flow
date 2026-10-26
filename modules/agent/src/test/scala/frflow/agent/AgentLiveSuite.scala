package frflow.agent

import cats.effect.{IO, Resource}
import frflow.agent.queue.*
import frflow.agent.request.*
import frflow.api.{Decide, Developer, Host, Inbox, LiveApi}
import frflow.check.Workspace
import frflow.fixtures.shelfKb
import frflow.protocol.*
import java.nio.file.{Files, Path}
import java.util.Comparator
import scala.util.Using

/** The agent layer over a project on disk: its files beside the ledger, the live API under it. */
class AgentLiveSuite extends munit.CatsEffectSuite:
  private val dir = ResourceFunFixture(Resource.make(IO.blocking(Files.createTempDirectory("frflow-agent")))(d =>
    IO.blocking(Using.resource(Files.walk(d))(_.sorted(Comparator.reverseOrder()).forEach(Files.delete(_))))))
  private def project(d: Path) = d.resolve("project")
  private def env(d: Path) = Map("FRFLOW_KEY" -> d.resolve("signing.key").toString)
  private def host(d: Path, kb: frflow.KnowledgeBase = shelfKb) =
    LiveApi(kb, Workspace(project(d), "../lean"), env(d)).map(Host(_, project(d), env(d)))
  private val dev = Developer("demo")

  dir.test("the developer asks; the agent answers the request; a rejected node is the agent's to replace") { d =>
    val why = "a shelf is not where picked books come from"
    for
      h <- host(d)
      a <- AgentApi.live(h)
      asked <- a.ask(Some(NodeId("OnlyGood")), "Say what makes an item good.", dev)
      id = asked.fold(r => fail(r.message), _.id)
      answered <- a.answer(id.value, "Books says it: a book is good when it is long enough.")
      unknown <- a.ask(Some(NodeId("Nope")), "Say more.", dev)
      empty <- a.ask(None, "  ", dev)
      _ <- h.api.decide(Decide.Reject(NodeId("FromList"), why), dev)
      v <- h.api.view.flatMap(a.read)
    yield
      assertEquals(answered, Right(id))
      assertEquals(v.requests.map(q => (q.id, q.node, q.status, q.answer)),
        List((id, Some(NodeId("OnlyGood")), RequestStatus.Answered, Some("Books says it: a book is good when it is long enough."))))
      assertEquals((unknown, empty), (Left(AgentRefusal.UnknownNode(NodeId("Nope"))), Left(AgentRefusal.NoText)))
      assert(v.forAgent.contains(ForAgent.Replace(NodeId("FromList"), dev.name, why)), v.forAgent)
      // the agent's files sit beside the ledger; FrFlow's view does not read them
      assert(Files.isRegularFile(AgentApi.requestsFile(project(d))))
  }

  dir.test("a project starts in chat: the words and questions recorded, IDEA.md written from them and accepted, then the root") { d =>
    import frflow.{KnowledgeBase, Node, True}
    val empty = KnowledgeBase("Toy", idea = "IDEA.md")()
    val toyRoot = Node.claim("A reader borrows exactly the books on the shelf that nobody else holds.",
      why = "The idea's purpose, as the developer confirmed it in chat.")(True)
    val idea = "# Toy\n\nA shelf of books readers borrow.\nFrom: Q1\n\n## Borrowing\nFrom: Q1, Q2\nA reader borrows a book nobody holds.\n"
    def write(text: String) = IO.blocking { Files.createDirectories(project(d)); Files.writeString(project(d).resolve("IDEA.md"), text) }
    for
      h <- host(d, empty)
      a <- AgentApi.live(h)
      // the developer's words, and the agent's questions, each with the answer it assumes
      _ <- a.said("A shelf of books that readers borrow.")
      q1 <- a.asked("Can a reader hold several books?", "Yes, any number.")
      q2 <- a.asked("Can two readers hold one book?", "No: a book is held by one reader at a time.")
      _ <- a.replied("Q1", "Yes.")
      talking <- h.api.view.flatMap(a.read)
      // the agent writes IDEA.md from the conversation: it waits for the developer
      _ <- write(idea)
      written <- h.api.view
      accepted <- h.api.decide(Decide.Accept(List(IdeaReview.Id), "it says what the shelf is for"), dev)
      confirmed <- h.api.view.flatMap(a.read)
      // then the root, proposed: decided after IDEA.md
      withRoot <- host(d, KnowledgeBase("Toy", idea = "IDEA.md")(toyRoot))
      proposed <- withRoot.api.view
      // a changed answer: a warning of the agent layer's, beside FrFlow's
      _ <- a.replied("Q1", "Yes, at most three.")
      warned <- withRoot.api.view.flatMap(a.read)
    yield
      assertEquals((q1.map(_.id), q2.map(_.id)), (Right("Q1"), Right("Q2")))
      assertEquals(talking.conversation.said.map(_.text), List("A shelf of books that readers borrow."))
      assertEquals(talking.conversation.unanswered.map(_.id), List("Q2"))
      assertEquals((talking.view.annotated.idea, talking.view.nodes), (None, Nil))
      assertEquals(Inbox.of(written).idea.map(_.state), Some(ReviewState.Proposed))
      assertEquals(accepted.map(_.decisions.map(_.node)), Right(List(IdeaReview.Id)))
      assertEquals((confirmed.view.annotated.idea.map(_.state), confirmed.warnings), (Some(ReviewState.Accepted), Nil))
      assertEquals(proposed.node(NodeId("ToyRoot")).map(r => (r.state, r.review.waitsFor)), Some((ReviewState.Proposed, None)))
      assert(warned.warnings.exists(_.contains("the answer to Q1 changed after IDEA.md was accepted")), warned.warnings)
      assert(!warned.view.warnings.exists(_.contains("Q1")), warned.view.warnings)
  }
