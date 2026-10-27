package frflow.cli

import cats.effect.{ExitCode, IO}
import cats.syntax.all.*
import com.monovore.decline.Command as Sub
import frflow.api.view.Stop
import frflow.api.{Lean, Opened, Shelf}
import frflow.cli.command.{Asked, Command, Commands}
import frflow.cli.term.Style
import frflow.core.name.NodeId
import frflow.decision.rules.Command as Decide

/** The command line as CI and the developer meet it: what parses, the exit codes, and what `find`, `check` and `ci`
  * say, over the API in memory.
  */
class CommandsSuite extends munit.CatsEffectSuite:
  private def parse(args: String) =
    Sub("frflow", Commands.header(Nil))(Commands.all(Nil)).parse(args.split(" ").toList, Map.empty)
  private val (nonNegative, sameAbove) = (NodeId("nonNegative"), NodeId("sameAbove"))
  private def decide(make: String => Decide, about: Option[NodeId], why: Option[String]) =
    Command.Decision(make, about, Asked(why, None, yes = true))

  test("every command parses, --plain before or after it; a usage error is the help with errors") {
    List("tree", "tree root", "show decide --full", "diff decide", "inbox", "review --as dev", "reject expiry -m no",
      "confirm -m same", "revisit root -m look", "gone old -m renamed --yes", "rebase --as ann --yes",
      "deciders --as ann", "render", "check", "check pick --json", "status --json", "ci", "export",
      "find some words", "scaffold pick").foreach(a => assert(parse(a).isRight, a))
    // the web view is an sbt task, not a command; the agent's commands are a layer's, not FrFlow's
    assert(List("serve", "ask decide name the user", "said hello").forall(parse(_).left.exists(_.errors.nonEmpty)))
    assertEquals(List("--plain tree", "tree --plain", "tree").map(parse(_).map(_._2)),
      List(Right(true), Right(true), Right(false)))
    parse("accept a b --revisit c -m why --yes") match
      case Right((Command.Decision(make, about, asked), _)) =>
        assertEquals((make("why"), about, asked), (Decide.Accept(List(NodeId("a"), NodeId("b")), "why",
          List(NodeId("c")), Map.empty), None, Asked(Some("why"), None, true)))
      case other                                            => fail(other.toString)
    assert(List("nope", "tree a b", "show", "deciders").forall(parse(_).left.exists(_.errors.nonEmpty)))
  }

  test("exit codes: status 1 until every node is accepted and proven, then 0; a usage error 2; no Lean 3") {
    for
      api                <- Opened.api(Opened.trusted)
      (open, _)          <- Cli.all(api, Command.Status(json = false))
      _                  <- Cli.accepted(api)
      (done, text)       <- Cli.all(api, Command.Status(json = false),
                              decide(Decide.Revisit(NodeId("nope"), _), Some(NodeId("nope")), Some("look again here")),
                              decide(Decide.Gone(NodeId("old"), _), Some(NodeId("old")), None))
      term               <- Scripted(Nil)
      stops              <- List(Stop.UnknownNode(nonNegative), Stop.NoLean, Stop.NoVersion("ledger"))
                              .traverse(Launch.failed(term, _))
    yield
      assertEquals(open, List(ExitCode(1)))
      assertEquals(done ++ stops, List(0, 2, 2, 2, 3, 1).map(ExitCode(_)))
      assert(text.contains("Nothing waits: every node is accepted and proven, or its code tested."), text)
  }

  test("find: the nodes that mention some words, each in a line; wrapped to a terminal's width") {
    for
      api   <- Opened.api(Opened.before)
      (_, t) <- Cli.all(api, Command.Find("negative NUMBER"), Command.Find("dragons"))
      term  <- Scripted(Nil)
      _     <- Cli.run(api, term, Command.Find("service gives"), Style.plain.copy(width = Some(40)))
      wide  <- term.output
    yield
      assert(t.contains("What mentions it\n  ! nonNegative  claim  proposed  The service never gives a negative " +
        "number."),
        t)
      assert(t.contains("Nothing governs or mentions \"dragons\""), t)
      assert(wide.size > 2 && wide.forall(Style.visible(_) <= 40), wide.mkString("\n"))
  }

  test("check: a node whose obligation Lean does not prove reads open, with Lean's message; proven when none is") {
    for
      failing       <- Opened.api(Opened.trusted, lean = Lean.Proving(Set("complete"), Set.empty))
      (codes, text) <- Cli.all(failing, Command.Check(None, json = false))
      proven        <- Opened.api(Opened.trusted)
      (fine, done)  <- Cli.all(proven, Command.Check(None, json = false))
    yield
      assertEquals((codes, fine), (List(ExitCode(1)), List(ExitCode(0))))
      assert(text.contains("o aboveMinusOne: open\n  complete: open\n"), text)
      assert(text.contains(": unsolved goals"), text)
      assert(done.contains("+ aboveMinusOne: proven"), done)
  }

  test("check: a claim whose code fails a generated case reads failed, with the case, shrunk") {
    Opened.api(Opened.project(Shelf.Careless.kb)).flatMap(Cli.all(_, Command.Check(None, json = false))).map {
      (codes, text) =>
        assertEquals(codes, List(ExitCode(1)))
        assert(text.contains("x nonNegative: fails a generated case: ("), text)
        assert(text.contains("its result breaks the claim (seed "), text)
    }
  }

  test("check: a claim whose code is tested, not proven, says it is tested; proven stays for what Lean proves") {
    Opened.api(Opened.before).flatMap(Cli.all(_, Command.Check(None, json = false))).map { (_, text) =>
      assert(text.contains("+ nonNegative: proven; its code tested on 200 cases"), text)
    }
  }

  test("check: code failing a claim that changed under it says the claim changed, on the node's line") {
    for
      ports         <- Opened.ports()
      _             <- Opened.over(Opened.before, ports).flatMap(Cli.accepted)
      strict        <- Opened.over(Opened.project(Shelves.Strict.kb), ports)
      (codes, text) <- Cli.all(strict, Command.Check(None, json = false))
    yield
      assertEquals(codes, List(ExitCode(1)))
      assert(text.contains("x nonNegative: the claim changed and its code did not: the code fails a case of the " +
        "changed claim: (0)"), text)
  }

  test("check and ci stream each level on stderr as Lean starts it; ci exits 0 only when complete, nothing warned") {
    for
      api          <- Opened.api(Opened.trusted)
      (first, t1)  <- Cli.all(api, Command.Ci)
      _            <- Cli.accepted(api)
      (second, _)  <- Cli.all(api, Command.Ci)
    yield
      assertEquals(first ++ second, List(ExitCode(1), ExitCode(0)))
      assert(t1.contains("error: check: level 1 of 2: nonNegative\nerror: check: level 2 of 2: aboveMinusOne"), t1)
  }

  test("a node gone from the model: show and diff say so; an unknown name is a usage error") {
    for
      ports         <- Opened.ports()
      _             <- Opened.over(Opened.before, ports).flatMap(Cli.accepted)
      fewer         <- Opened.over(Opened.project(Shelves.Fewer.kb), ports)
      (codes, text) <- Cli.all(fewer, Command.Show(sameAbove, frflow.cli.text.Depth.Normal), Command.Diff(sameAbove),
                         Command.Inbox, Command.Show(NodeId("nope"), frflow.cli.text.Depth.Normal))
    yield
      assertEquals(codes, List(0, 0, 0, 2).map(ExitCode(_)))
      assertEquals(text.linesIterator.count(_.startsWith("sameAbove is gone from the model")), 2, text)
      assert(text.contains("Gone from the model (gone NODE agrees it is gone)\n  sameAbove"), text)
      assert(text.contains("error: unknown node nope"), text)
  }

  test("accept or reject a node gone from the model: rejecting it agrees it is gone, accepting it is refused") {
    val why = Some("the part is no longer needed")
    for
      ports         <- Opened.ports()
      _             <- Opened.over(Opened.before, ports).flatMap(Cli.accepted)
      fewer         <- Opened.over(Opened.project(Shelves.Fewer.kb), ports)
      (codes, text) <- Cli.all(fewer, decide(n => Decide.Accept(List(sameAbove), n, Nil, Map.empty), Some(sameAbove),
                         why), decide(Decide.Reject(sameAbove, _, None), Some(sameAbove), why))
      view          <- fewer.reading.view
    yield
      assertEquals(codes, List(ExitCode(1), ExitCode(0)))
      assert(text.contains("error: sameAbove is gone from the model: it cannot be decided on"), text)
      assert(text.contains("sameAbove is gone from the model: recording that you agree it is gone"), text)
      assertEquals(view.gone, Nil)
  }
