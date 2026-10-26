package frflow.agent

import cats.effect.{ExitCode, IO}
import cats.syntax.all.*
import com.monovore.decline.Command as Sub
import frflow.agent.queue.*
import frflow.agent.request.*
import frflow.api.*
import frflow.check.TempDirs
import frflow.cli.*
import frflow.ledger.JsonStore
import frflow.protocol.*
import java.time.Instant

/** The agent layer on the command line: its commands, and what it adds to FrFlow's views, over the in-memory API with the
  * agent's files in a directory of the test's own.
  */
class AgentCliSuite extends munit.CatsEffectSuite with TempDirs:
  private val st = Style(color = false, unicode = false, width = None)
  private def parse(args: String) =
    Sub("frflow", Commands.header(List(Agent)))(Commands.all(List(Agent))).parse(args.split(" ").toList, Map.empty)

  private val requests = List(
    Request(RequestId("R1"), Some(NodeId("NeedsGrant")), "Add an example: a revoked grant refuses access.", Sample.by,
      Instant.parse("2026-01-03T10:00:00Z"), RequestStatus.Answered, Some("Added the example under Decide; it is proven."), None),
    Request(RequestId("R2"), None, "Users can see who accessed their records.", Sample.by, Instant.parse("2026-01-03T11:00:00Z"), RequestStatus.Open))

  /** The fake API, and a host whose directory holds the agent's files (`rs` as the requests). */
  private def setUp(rs: List[Request] = requests, api: IO[FakeApi] = FakeApi()): IO[(FakeApi, Host)] =
    val dir = tempDir("frflow-agent-cli")
    for
      a <- api
      _ <- JsonStore.make(AgentApi.requestsFile(dir), List.empty[Request]).flatMap(_.update[Nothing, Unit](_ => Right((rs, ()))))
    yield (a, Host(a, dir, Map.empty))
  private def dispatch(host: Host, term: Terminal)(c: Command) = Dispatch(host.api, term, st, List(Agent), Some(host))(c)
  private def run(host: Host, term: Terminal)(args: String*) =
    Sub("frflow", "")(Commands.all(List(Agent))).parse(if args.size == 1 then args.head.split(" ").toList else args.toList, Map.empty) match
      case Right((c, _)) => dispatch(host, term)(c)
      case Left(help) => IO(fail(help.toString))

  test("the agent's commands parse after FrFlow's; the help says what the layer adds") {
    List("ask Decide name the user", "ask --idea more", "close R1 R2", "context Decide", "answer R1 done it",
      "said a shared CRM for many companies", "asked can a company share a record --assume yes until a date", "replied Q1 yes",
      "conversation --json", "tree").foreach(a => assert(parse(a).isRight, a))
    // a question needs the answer assumed
    assert(parse("asked who decides").left.exists(_.errors.nonEmpty))
    assert(Commands.header(List(Agent)).contains("With an AI agent"))
    assert(!Commands.header().contains("agent"))
  }

  test("the agent records the conversation: what was said, each question with the answer assumed, the reply; inbox lists the open ones") {
    for
      (_, host) <- setUp()
      term <- Scripted(Nil, interactive = false)
      codes <- List(List("said", "A CRM shared by many companies."), List("asked", "Can a company share a record?", "--assume", "Yes, until a date."),
        List("asked", "Who may unshare it?", "--assume", "Only the owning company."), List("replied", "q1", "Yes, until a date or for good."))
        .traverse(a => run(host, term)(a*))
      unknown <- run(host, term)("replied Q9 no")
      _ <- run(host, term)("conversation")
      _ <- dispatch(host, term)(Command.Inbox(json = false))
      out <- term.output
    yield
      assertEquals(codes, List.fill(4)(ExitCode.Success))
      assertEquals(unknown, ExitCode(2))
      val text = out.mkString("\n")
      List("recorded [Q1]: ask it in chat, with the answer you assume", "recorded the reply to [Q1]", "no question Q9 in the conversation",
        "What you said", "  A CRM shared by many companies.", "  [Q1] Can a company share a record?", "    assumed: Yes, until a date.",
        "    you: Yes, until a date or for good.", "    no reply yet", "Questions the agent asked: answer them in chat",
        "  [Q2] Who may unshare it?", "1 question(s) for the developer to answer in chat").foreach(l => assert(text.contains(l), s"$l\n$text"))
  }

  test("the inbox: requests, answers to read, the agent's queue; a node asked of the agent waits with it, not in the queue") {
    for
      (api, host) <- setUp()
      v <- api.view
      asked = Request(RequestId("R3"), Some(NodeId("Decide")), "Say 'them' as 'that user'.", Sample.by, Sample.at, RequestStatus.Open,
        seen = v.node(NodeId("Decide")).map(_.review.version))
      (_, held) <- setUp(requests :+ asked)
      (_, moved) <- setUp(requests :+ asked.copy(seen = Some(Version("an older version"))))
      term <- Scripted(Nil, interactive = false)
      _ <- dispatch(held, term)(Command.Inbox(json = false))
      out <- term.output
      a <- Agent.api(held).flatMap(_.read(v))
      heldInbox <- api.inbox(_ => IO.pure(a.held))
      b <- Agent.api(moved).flatMap(_.read(v))
    yield
      val text = out.mkString("\n")
      List("Requests from the developer", "[R2] on the idea", "Answers to read (close REQUEST when read)",
        "agent: Added the example under decide", "With the agent: asked, until it answers or changes the node",
        "For the agent", "forever: rejected by dev: sessions must end: a stolen token would work forever")
        .foreach(l => assert(text.contains(l), s"$l\n$text"))
      assertEquals(a.forAgent, List(ForAgent.Replace(NodeId("Forever"), Sample.by, "sessions must end: a stolen token would work forever")))
      assertEquals((a.open.map(_.id), a.answers.map(_.id)), (List(RequestId("R2"), RequestId("R3")), List(RequestId("R1"))))
      assertEquals(heldInbox.aside.map(_.id), List(NodeId("Decide")))
      assert(!heldInbox.queue.exists(_.node.id == NodeId("Decide")))
      // once the node moved since it was asked about, it is back with the developer
      assertEquals(b.held, Set.empty[NodeId])
  }

  test("review: [?] asks the agent for a change instead of deciding, and the node is with the agent") {
    val typed = List("a", "the new parts are proven to make it", "?", "Name the user as 'that user'.", "a", "an hour bounds a stolen token", "y")
    for
      (api, host) <- setUp(Nil)
      term <- Scripted(typed)
      code <- ReviewSession(api, term, st, v => Agent.contribute(host, v)).run(None)
      out <- term.output
      v <- api.view.flatMap(v => Agent.api(host).flatMap(_.read(v)))
    yield
      assertEquals(code, ExitCode.Success)
      assert(out.exists(_.contains("[?]ask")), out.mkString("\n"))
      assert(out.exists(_.contains(": Decide is with the agent until it answers or changes it")), out.mkString("\n"))
      assertEquals(v.requests.map(q => (q.node, q.text)), List((Some(NodeId("Decide")), "Name the user as 'that user'.")))
      assert(v.view.node(NodeId("Decide")).exists(v.withAgent))
  }

  test("context: the node in full, its requests, and what the agent works by") {
    for
      (_, host) <- setUp()
      term <- Scripted(Nil, interactive = false)
      code <- run(host, term)("context NeedsGrant")
      out <- term.output
    yield
      assertEquals(code, ExitCode.Success)
      val text = out.mkString("\n")
      List("Requests", "[R1] answered", "The developer decides; you propose.").foreach(l => assert(text.contains(l), s"$l\n$text"))
  }
