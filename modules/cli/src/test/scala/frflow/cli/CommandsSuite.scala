package frflow.cli

import cats.effect.{ExitCode, IO}
import cats.syntax.all.*
import com.monovore.decline.Command as Sub
import frflow.api.*
import frflow.cli.command.*
import frflow.cli.text.*
import frflow.protocol.*

/** The command line as CI meets it: what parses, and the exit codes. */
class CommandsSuite extends munit.CatsEffectSuite:
  private val st = Style(color = false, unicode = false, width = None)
  private def parse(args: String) = Sub("frflow", Commands.header())(Commands.all()).parse(args.split(" ").toList, Map.empty)

  test("every command parses, --plain before or after it; a usage error is the help with errors") {
    List("tree", "tree Root --json", "show Decide --full --json", "diff Decide", "inbox --json", "review --as dev", "reject Expiry --reason no",
      "confirm -m same", "revisit Root -m look", "gone Old -m renamed --yes", "render", "check", "check Pick --json", "status --json", "ci",
      "find some words", "scaffold Pick")
      .foreach(a => assert(parse(a).isRight, a))
    // the web view is an sbt task, not a command; the agent's commands are a layer's, not FrFlow's
    assert(List("serve", "ask Decide name the user", "said hello").forall(parse(_).left.exists(_.errors.nonEmpty)))
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
      complete <- FakeApi(Sample.decided, Sample.ledger).flatMap(Dispatch(_, term, st)(Command.Status(json = false)))
      out <- term.output
      unknown <- FakeApi().flatMap(Dispatch(_, term, st)(Command.Decision(Decide.Revisit(NodeId("Nope"), _), Asked(Some("look"), None, yes = true))))
      noReason <- FakeApi().flatMap(Dispatch(_, term, st)(Command.Decision(Decide.Gone(NodeId("Old"), _), Asked(None, None, yes = true))))
      failed <- List(FrFlowError.UnknownNode(NodeId("Nope")), FrFlowError.ModelProblems(List("a cycle")), FrFlowError.LeanMissing).traverse(FrFlowApp.failed(term, _))
    yield
      assertEquals((open, complete), (ExitCode(1), ExitCode.Success))
      assert(out.contains("Nothing waits: every node is accepted and proven."), out)
      assertEquals((unknown, noReason, failed), (ExitCode(2), ExitCode(2), List(2, 1, 3).map(ExitCode(_))))
  }

  test("find: the nodes that mention some words, each with its sentence; wrapped to a terminal's width") {
    def find(q: String, st: Style) = FakeApi().flatMap(api => api.view.flatMap(v => api.find(v, q).map(f => ReportText.found(f, v, st))))
    find("stolen token", st).map { out =>
      assertEquals(out.headOption, Some("What mentions it:"))
      assert(out.contains("- Expiry: A session ends an hour after sign-in."), out)
    } *> List("stolen token", "user", "src/main/scala/auth/Cache.scala", "dragons").traverse_(q => find(q, st.copy(width = Some(40))).map { out =>
      assert(out.size > 1 && out.forall(Style.visible(_) <= 40), out.mkString("\n"))
    })
  }

  test("check: a node Lean proved with its impl open reads open, as check exits on it; proven when nothing is open") {
    def checked(c: CheckedNode) = FakeApi().flatMap(_.view).map(v => ReportText.check(CheckReport(List(c), v, Overview.of(v)), st).head)
    val proven = CheckedNode(NodeId("Decide"), CheckStatus.Proven, Nil, Nil, Nil, None, Nil, None)
    (checked(proven.copy(notProven = List(ObligationName.Impl))), checked(proven)).mapN { (open, done) =>
      assertEquals(open, "o Decide: open (impl not proven)")
      assertEquals(done, "+ Decide: proven")
    }
  }

  test("check: a contract whose code fails a generated case reads failed, with the case, shrunk") {
    val failure = TestFailure("(\"t1\", Path(\"/b\")) ⇒ Some(UserId(\"alice\"))", "returned Some(UserId(\"alice\")), which Decide refuses", 1, 0, 1)
    val failing = CheckedNode(NodeId("Decide"), CheckStatus.Proven, Nil, Nil, Nil, None, Nil, None, Some(failure))
    FakeApi().flatMap(_.view).map { v =>
      val text = ReportText.check(CheckReport(List(failing), v, Overview.of(v)), st)
      assertEquals(text.take(3), List("x Decide: failed",
        "  its code fails a generated case: (\"t1\", Path(\"/b\")) ⇒ Some(UserId(\"alice\"))",
        "    returned Some(UserId(\"alice\")), which Decide refuses"))
      assert(!CheckReport(List(failing), v, Overview.of(v)).ok)
    }
  }

  test("find: a path that names no file says so; one no node governs says that") {
    def find(q: String) = FakeApi().flatMap(api => api.view.flatMap(v => api.find(v, q).map(f => ReportText.found(f, v, st).mkString(" "))))
    (find("nope/Cache.scala"), find("src/main/scala/auth/Cache.scala")).mapN { (missing, ungoverned) =>
      assertEquals(missing, "There is no file or directory nope/Cache.scala (paths are relative to the project's directory).")
      assert(ungoverned.startsWith("No node governs src/main/scala/auth/Cache.scala"), ungoverned)
    }
  }

  test("a node gone from the model: show and diff say so, with its last decision; renamed, when a node says the same") {
    // StoreKeeps renamed: the same statement under another name.
    val snapshot = Sample.decided.copy(nodes = Sample.decided.nodes.map(n => if n.id == Sample.store.id then n.copy(id = NodeId("StoreReturnsLast")) else n))
    for
      api <- FakeApi(snapshot, Sample.ledger)
      term <- Scripted(Nil, interactive = false)
      codes <- List(Command.Show(NodeId("StoreKeeps"), Depth.Normal, json = false), Command.Diff(NodeId("StoreKeeps")), Command.Inbox(json = false),
        Command.Show(NodeId("Nope"), Depth.Normal, json = false)).traverse(c => Dispatch(api, term, st)(c).handleErrorWith(FrFlowApp.failed(term, _)))
      out <- term.output
    yield
      assertEquals(codes, List(ExitCode.Success, ExitCode.Success, ExitCode.Success, ExitCode(2)))
      assertEquals(out.count(_ == "- StoreKeeps  gone from the model"), 2, out.mkString("\n"))
      assertEquals(out.count(_ == "  last accepted by dev (2026-01-02 10:00): StoreKeeps holds as stated"), 2, out.mkString("\n"))
      assertEquals(out.count(_ == "  renamed to StoreReturnsLast (it says the same): gone StoreKeeps agrees that it is gone"), 2, out.mkString("\n"))
      assert(out.contains("  StoreKeeps  renamed to StoreReturnsLast: The store returns what was last written."), out.mkString("\n"))
      assert(out.contains("error: unknown node Nope"), out.mkString("\n"))
  }

  test("IDEA.md waits for the developer, first: the root is decided after it, and accepting it twice is refused") {
    val idea = "# Shelf\n\nA shelf hands out the good books.\n\n## Picking\nFrom: Q1\nOnly long books are picked.\n"
    for
      api <- FakeApi(Sample.snapshot.copy(idea = idea), Sample.ledgerNow)
      term <- Scripted(Nil, interactive = false)
      before <- api.view
      root = before.snapshot.root.flatMap(before.node).get
      _ <- Dispatch(api, term, st)(Command.Inbox(json = false))
      refused <- Dispatch(api, term, st)(Command.Decision(Decide.Accept(List(root.id), _), Asked(Some("as decided"), None, yes = true)))
      accepted <- Dispatch(api, term, st)(Command.Decision(Decide.Accept(List(IdeaReview.Id), _), Asked(Some("it says what the shelf is for"), None, yes = true)))
      after <- api.view
      again <- Dispatch(api, term, st)(Command.Decision(Decide.Accept(List(IdeaReview.Id), _), Asked(Some("again"), None, yes = true)))
      out <- term.output
    yield
      assertEquals(before.annotated.idea.map(_.state), Some(ReviewState.Proposed))
      assertEquals(root.review.waitsFor, Some(IdeaReview.Id))
      assertEquals((refused, accepted, again), (ExitCode(1), ExitCode.Success, ExitCode(1)))
      assertEquals(after.annotated.idea.map(_.state), Some(ReviewState.Accepted))
      assertEquals(after.snapshot.root.flatMap(after.node).flatMap(_.review.waitsFor), None)
      val text = out.mkString("\n")
      List("IDEA.md, first", "IDEA.md, not accepted yet: read it, then accept IDEA",
        "error: accept IDEA first: what rests on it is decided after it", "error: IDEA is already accepted")
        .foreach(l => assert(text.contains(l), s"$l\n$text"))
  }
