package frflow.cli

import cats.effect.ExitCode
import cats.syntax.all.*
import com.monovore.decline.Command as Sub
import frflow.api.*
import frflow.protocol.*

/** The command line as CI and agents meet it: what parses, and the exit codes. */
class CommandsSuite extends munit.CatsEffectSuite:
  private val st = Style(color = false, unicode = false, width = None)
  private def parse(args: String) = Sub("frflow", Commands.header)(Commands.all).parse(args.split(" ").toList, Map.empty)

  test("every command parses, --plain before or after it; a usage error is the help with errors") {
    List("tree", "tree Root --json", "show Decide --full --json", "diff Decide", "inbox --json", "review --as dev", "reject Expiry --reason no",
      "confirm -m same", "revisit Root -m look", "gone Old -m renamed --yes", "ask Decide name the user", "ask --idea more", "close R1 R2",
      "render", "check", "check Pick --json", "status --json", "ci", "context Decide", "find some words", "scaffold Pick", "answer R1 done it")
      .foreach(a => assert(parse(a).isRight, a))
    assertEquals(List("--plain tree", "tree --plain", "tree").map(parse(_).map(_._2)), List(Right(true), Right(true), Right(false)))
    parse("accept A B --revisit C -m why --yes") match
      case Right((Command.Decision(make, asked), _)) =>
        assertEquals((make("why"), asked), (Decide.Accept(List(NodeId("A"), NodeId("B")), "why", List(NodeId("C"))), Asked(Some("why"), None, true)))
      case other => fail(other.toString)
    assert(List("nope", "tree A B", "show").forall(parse(_).left.exists(_.errors.nonEmpty)))
  }

  test("exit codes: status 1 until every node is accepted and proven, then 0; a usage error 2; no Lean 3") {
    for
      term <- Scripted(Nil, interactive = false)
      open <- FakeApi().flatMap(Dispatch(_, term, st)(Command.Status(json = false)))
      complete <- FakeApi(Sample.decided, Sample.ledger, Nil).flatMap(Dispatch(_, term, st)(Command.Status(json = false)))
      out <- term.output
      unknown <- FakeApi().flatMap(Dispatch(_, term, st)(Command.Answer("R9", "done")))
      noReason <- FakeApi().flatMap(Dispatch(_, term, st)(Command.Decision(Decide.Gone(NodeId("Old"), _), Asked(None, None, yes = true))))
      failed <- List(FrFlowError.UnknownNode(NodeId("Nope")), FrFlowError.ModelProblems(List("a cycle")), FrFlowError.LeanMissing).traverse(FrFlowApp.failed(term, _))
    yield
      assertEquals((open, complete), (ExitCode(1), ExitCode.Success))
      assert(out.contains("Nothing waits: every node is accepted and proven."), out)
      assertEquals((unknown, noReason, failed), (ExitCode(2), ExitCode(2), List(2, 1, 3).map(ExitCode(_))))
  }

  test("find: the nodes that mention some words, each with its sentence") {
    FakeApi().flatMap(api => api.view.flatMap(v => api.find(v, "stolen token").map(f => ReportText.found(f, v, st)))).map { out =>
      assertEquals(out.headOption, Some("What mentions it:"))
      assert(out.contains("- Expiry: A session ends an hour after sign-in."), out)
    }
  }
