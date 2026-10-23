package frflow.cli

import cats.effect.{ExitCode, IO, Ref}
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
      "render", "check", "check Pick --json", "status --json", "ci", "context Decide", "find some words", "scaffold Pick", "answer R1 done it",
      "said a shared CRM for many companies", "asked can a company share a record --assume yes until a date", "replied Q1 yes", "conversation --json")
      .foreach(a => assert(parse(a).isRight, a))
    // the web view is an sbt task, not a command; a question needs the answer assumed
    assert(List("serve", "asked who decides").forall(parse(_).left.exists(_.errors.nonEmpty)))
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
      api <- FakeApi(snapshot, Sample.ledger, Nil)
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

  test("the agent records the conversation: what was said, each question with the answer assumed, the reply; inbox lists the open ones") {
    for
      api <- FakeApi()
      term <- Scripted(Nil, interactive = false)
      codes <- List(Command.Said("A CRM shared by many companies."), Command.QuestionAsked("Can a company share a record?", "Yes, until a date."),
        Command.QuestionAsked("Who may unshare it?", "Only the owning company."), Command.Replied("q1", "Yes, until a date or for good."))
        .traverse(Dispatch(api, term, st)(_))
      unknown <- Dispatch(api, term, st)(Command.Replied("Q9", "no"))
      _ <- Dispatch(api, term, st)(Command.Conversation(json = false))
      _ <- Dispatch(api, term, st)(Command.Inbox(json = false))
      out <- term.output
    yield
      assertEquals(codes, List.fill(4)(ExitCode.Success))
      assertEquals(unknown, ExitCode(2))
      val text = out.mkString("\n")
      List("recorded [Q1]: ask it in chat, with the answer you assume", "recorded the reply to [Q1]", "error: no question Q9 in the conversation",
        "What you said", "  A CRM shared by many companies.", "  [Q1] Can a company share a record?", "    assumed: Yes, until a date.",
        "    you: Yes, until a date or for good.", "    no reply yet", "Questions the agent asked: answer them in chat",
        "  [Q2] Who may unshare it?", "1 question(s) for the developer to answer in chat").foreach(l => assert(text.contains(l), s"$l\n$text"))
  }

  test("IDEA.md waits for the developer, first: the root is decided after it, and accepting it twice is refused") {
    val idea = "# Shelf\n\nA shelf hands out the good books.\n\n## Picking\nFrom: Q1\nOnly long books are picked.\n"
    for
      api <- FakeApi(Sample.snapshot.copy(idea = idea), Sample.ledgerNow, Nil)
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
      List("IDEA.md, first", "IDEA.md, written by the agent from your conversation: read it, then accept IDEA",
        "error: accept IDEA first: what rests on it is decided after it", "error: IDEA is already accepted")
        .foreach(l => assert(text.contains(l), s"$l\n$text"))
  }
