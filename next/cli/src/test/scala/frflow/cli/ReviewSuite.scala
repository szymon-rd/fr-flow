package frflow.cli

import cats.effect.{ExitCode, IO, Ref}
import frflow.api.{FrFlowApi, Opened}
import frflow.cli.command.{Asked, Command}
import frflow.cli.review.{ReviewKey, ReviewSession}
import frflow.cli.term.Style
import frflow.cli.text.Contribution
import frflow.core.name.NodeId
import frflow.decision.ledger.Action
import frflow.decision.review.ReviewState
import frflow.decision.rules.Command as Decide

/** The review and the deciding commands on scripted input, over the API in memory. */
class ReviewSuite extends munit.CatsEffectSuite:
  private val st = Style.plain.copy(width = Some(100))
  private val (nonNegative, sameAbove) = (NodeId("nonNegative"), NodeId("sameAbove"))

  private def review(api: FrFlowApi[IO], typed: List[String], keys: List[ReviewKey] = Nil) =
    Scripted(typed).flatMap(t => ReviewSession(api, t, st, _ => IO.pure(Contribution.empty), keys).run(None)
      .flatMap(code => t.text.map(code -> _)))

  private def state(api: FrFlowApi[IO], id: NodeId) =
    api.reading.view.map(_.node(id).map(n => n.review.standing.state -> n.review.decisions.binding.map(_.action)))

  /** Every node accepted; then the model as `p` has it, over the same ledger. */
  private def moved(p: frflow.api.Project[IO]) =
    Opened.ports().flatMap(ports => Opened.over(Opened.before, ports).flatMap(Cli.accepted) >> Opened.over(p, ports))

  test("review: a layer's key instead of a decision, then the node it skipped is not offered again") {
    for
      api       <- Opened.api(Opened.before)
      noted     <- Ref.of[IO, List[(NodeId, String)]](Nil)
      key        = ReviewKey("n", "[n]ote", (_, n, term, _) => term.read("Note: ").flatMap(t =>
                     noted.update(_ :+ (n.id -> t.getOrElse(""))) >> term.out(s"noted on ${n.id}")))
      (code, t) <- review(api, List("n", "name the number plainly", "q"), List(key))
      notes     <- noted.get
    yield
      assertEquals(code, ExitCode.Success)
      assert(t.contains("[a]ccept [r]eject [s]kip [v]iew [q]uit [n]ote: n"), t)
      assertEquals(notes, List(nonNegative -> "name the number plainly"))
  }

  test("without a terminal: review is refused, and a decision needs --yes; with it, it is recorded") {
    def reject(yes: Boolean) = Command.Decision(Decide.Reject(nonNegative, _, None), Some(nonNegative),
      Asked(Some("a negative number is fine here"), None, yes))
    for
      api        <- Opened.api(Opened.before)
      term       <- Scripted(Nil, interactive = false)
      refused    <- ReviewSession(api, term, st, _ => IO.pure(Contribution.empty), Nil).run(None)
      (codes, t) <- Cli.all(api, reject(yes = false), reject(yes = true))
      after      <- state(api, nonNegative)
    yield
      assertEquals(refused :: codes, List(ExitCode(2), ExitCode(1), ExitCode(0)))
      assert(t.contains("pass --yes"), t)
      assertEquals(after.map(_._1), Some(ReviewState.Rejected))
  }

  test("on a terminal a decision shows what it records and asks first") {
    val accept = Command.Decision(n => Decide.Accept(List(nonNegative), n, Nil, Map.empty), Some(nonNegative),
      Asked(None, None, yes = false))
    for
      api  <- Opened.api(Opened.before)
      term <- Scripted(List("it says what the service must do", "y"))
      code <- Cli.run(api, term, accept)
      t    <- term.text
    yield
      assertEquals(code, ExitCode.Success)
      assert(t.contains("Why (kept as part of the theory)? it says what the service must do"), t)
      assert(t.contains("This records, as ann:\n  - accepted nonNegative\nRecord it? [y/N] y"), t)
      assert(t.contains("Recorded, signed by ann:\n  - accepted nonNegative"), t)
  }

  test("a refused decision exits 1 and says why") {
    val accept = Command.Decision(n => Decide.Accept(List(sameAbove), n, Nil, Map.empty), Some(sameAbove),
      Asked(Some("it says what the service must do"), None, yes = true))
    Opened.api(Opened.before).flatMap(Cli.all(_, accept)).map { (codes, t) =>
      assertEquals(codes, List(ExitCode(1)))
      assert(t.contains("refused: decide nonNegative first: what rests on it is decided after it"), t)
    }
  }

  test("a node waiting for another offers no [a]ccept, and says once what it waits for") {
    for
      api       <- Opened.api(Opened.before)
      (code, t) <- review(api, List("s", "a", "q"))
    yield
      assertEquals(code, ExitCode.Success)
      assert(t.contains("\n[s]kip [v]iew [q]uit: a"), t)
      assertEquals(t.linesIterator.count(_ == "one of: q s v"), 1, t)
      assertEquals(t.linesIterator.count(_.contains("decide nonNegative first")), 1, t)
  }

  test("a mistyped name at the revisit prompt is asked again: the reason and the node are kept") {
    val typed = List("a", "nope", "sameAbove", "a stricter bound is what the service needs", "y", "q")
    for
      api       <- moved(Opened.after)
      (_, t)    <- review(api, typed)
      claim     <- state(api, nonNegative)
      part      <- api.reading.view.map(_.node(sameAbove).map(_.review.standing))
    yield
      assert(t.contains("not a decision below nonNegative: nope"), t)
      assertEquals(t.linesIterator.count(_.startsWith("Revisit any decision below")), 2, t)
      assertEquals(claim, Some(ReviewState.Accepted -> Some(Action.Accept)))
      assert(part.exists(_.causes.contains(frflow.decision.review.Cause.Revisit)), part)
  }

  test("what moved only with a node: the inbox says it waits for it, and accepting the node confirms it") {
    for
      api      <- moved(Opened.after)
      (_, box) <- Cli.all(api, Command.Inbox)
      (_, t)   <- review(api, List("a", "", "the bound says the same, in other words", "y", "q"))
      part     <- state(api, sameAbove)
    yield
      assert(box.contains("    decide nonNegative first: what rests on it is decided after it"), box)
      assert(t.contains("Recorded, signed by ann:"), t)
      assertEquals(part, Some(ReviewState.Accepted -> Some(Action.Confirm)))
  }

  test("the mechanical batch: a node whose new part Lean proves makes it is confirmed with one reason") {
    for
      api    <- moved(Opened.project(frflow.api.Shelf.Grown.kb))
      _      <- Opened.checked(api.proving.check(None))
      (_, t) <- review(api, List("a", "a new part makes it as before", "q"))
      claim  <- state(api, nonNegative)
    yield
      assert(t.contains("1 mechanical decision(s): Lean proves them again, and nothing in them is a choice"), t)
      assertEquals(claim, Some(ReviewState.Accepted -> Some(Action.Confirm)))
  }
