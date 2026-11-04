package frflow.agent

import cats.effect.{ExitCode, IO}
import cats.syntax.all.*
import com.monovore.decline.Command as Sub
import frflow.agent.work.AgentApi
import frflow.api.{FrFlowApi, Opened}
import frflow.cli.command.{Commands, Dispatch}
import frflow.cli.review.ReviewSession
import frflow.cli.term.Style
import frflow.cli.{Cli, Launch, Scripted}
import frflow.core.name.NodeId
import frflow.decision.review.ReviewState

/** The agent layer on the command line, over the API in memory and the layer's records in memory: its commands, what
  * it adds to FrFlow's views, its key in the review; none of it decides.
  */
class AgentCliSuite extends munit.CatsEffectSuite:
  private val st = Style.plain
  private val nonNegative = NodeId("nonNegative")

  /** The API over the shelf, and the agent's layer over records in memory. */
  private def opened: IO[(FrFlowApi[IO], AgentLayer, AgentApi[IO])] =
    Opened.api(Opened.before).flatMap(api =>
      AgentApi.inMemory[IO](api.reading).map(a => (api, AgentLayer(_ => IO.pure(a)), a)))

  /** Each command line as typed, on one terminal: the exit codes and all that was written. */
  private def typed(api: FrFlowApi[IO], layer: AgentLayer, lines: List[String]*): IO[(List[ExitCode], String)] =
    Scripted(Nil, interactive = false).flatMap(t => lines.toList.traverse { args =>
      Sub("frflow", "")(Commands.all(List(layer))).parse(args, Map.empty) match
        case Right((c, _)) => Dispatch(api, Cli.host(api), t, st)(List(layer))(c).handleErrorWith(Launch.failed(t, _))
        case Left(help)    => IO(fail(help.toString))
    }.flatMap(codes => t.text.map(codes -> _)))

  test("the agent's commands parse after FrFlow's; the help says what the layer adds") {
    val layer = AgentLayer(_ => IO.raiseError(AssertionError("not opened")))
    def parse(a: String) = Sub("frflow", "")(Commands.all(List(layer))).parse(a.split(" ").toList, Map.empty)
    List("ask nonNegative name the number", "ask --idea more", "close R1 R2", "context nonNegative",
      "answer R1 done it", "said a shelf of numbers", "asked can it be negative --assume no", "replied q1 no",
      "conversation --json", "tree").foreach(a => assert(parse(a).isRight, a))
    assert(parse("asked who decides").left.exists(_.errors.nonEmpty))
    assert(Commands.header(List(layer)).contains("With an AI agent"))
    assert(!Commands.header(Nil).contains("agent"))
  }

  test("the agent records the conversation: what was said, each question with the answer assumed, the reply") {
    for
      (api, layer, a) <- opened
      (codes, _)      <- typed(api, layer, List("said", "A shelf of numbers."), List("asked", "Can a number be " +
                           "negative?", "--assume", "No, never."))
      q               <- api.reading.view.flatMap(a.read).map(_.conversation.questions.map(_.id))
      (more, text)    <- typed(api, layer, List("replied", q.mkString, "No, and zero is fine."),
                           List("replied", "q0", "no"), List("conversation"))
    yield
      assertEquals(codes ++ more, List(0, 0, 0, 2, 0).map(ExitCode(_)))
      assert(text.contains("What you said\n  A shelf of numbers."), text)
      assert(text.contains("  assumed: No, never.\n    you: No, and zero is fine.") ||
        text.contains("  assumed: No, never.\n  you: No, and zero is fine."), text)
      assert(text.contains("error: no question q0 in the conversation"), text)
  }

  test("the inbox: requests, answers to read, the agent's queue; a node asked of the agent waits with it, not in the " +
    "queue") {
    for
      (api, layer, a) <- opened
      _               <- a.ask(Some(nonNegative), "name the number plainly", "ann")
      _               <- a.ask(None, "the shelf may hold words too", "ann")
      (_, text)       <- typed(api, layer, List("inbox"))
    yield
      assert(text.contains("Requests from the developer\n  [R"), text)
      assert(text.contains("With the agent: asked, until it answers or changes the node\n  ! nonNegative"), text)
      assert(!text.contains("To decide, in order (review, or accept / reject NODE)\n  ! nonNegative"), text)
      assert(text.contains("1 asked of the agent"), text)
  }

  test("review: [?] asks the agent for a change instead of deciding, and the node is with the agent") {
    for
      (api, layer, a) <- opened
      term            <- Scripted(List("?", "name the number plainly", "q"))
      code            <- ReviewSession(api, term, st, v => layer.contribute(Cli.host(api), v, st),
                           layer.keys(Cli.host(api))).run(Some("ann"))
      text            <- term.text
      view            <- api.reading.view
      held            <- a.read(view).map(_.held)
    yield
      assertEquals(code, ExitCode.Success)
      assert(text.contains("[a]ccept [r]eject [s]kip [v]iew [q]uit [?]ask: ?"), text)
      assert(text.contains("nonNegative is with the agent until it answers or changes it"), text)
      assertEquals(held, Set(nonNegative))
      assertEquals(view.node(nonNegative).map(_.review.standing.state), Some(ReviewState.Proposed))
  }

  test("context: the node in full, its requests, and what the agent works by") {
    for
      (api, layer, a) <- opened
      _               <- a.ask(Some(nonNegative), "name the number plainly", "ann")
      (codes, text)   <- typed(api, layer, List("context", "nonNegative"))
    yield
      assertEquals(codes, List(ExitCode(0)))
      assert(text.contains("What it mentions"), text)
      assert(text.contains("Requests\n  [R"), text)
      assert(text.contains("The developer decides; you propose"), text)
  }

  test("none of the agent's commands decides: the ledger is as it was after each") {
    for
      (api, layer, _) <- opened
      before          <- api.reading.view
      _               <- typed(api, layer, List("ask", "nonNegative", "more"), List("answer", "nonNegative", "done"),
                           List("said", "hello there"), List("context", "nonNegative"), List("close", "R0"))
      after           <- api.reading.view
    yield assertEquals(after.nodes.map(_.review), before.nodes.map(_.review))
  }
