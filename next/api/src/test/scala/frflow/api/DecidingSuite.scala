package frflow.api

import cats.syntax.all.*
import frflow.api.Opened.id
import frflow.api.view.Warning
import frflow.api.view.diff.DiffLine
import frflow.decision.ledger.{Action, Uncounted}
import frflow.decision.review.{Cause, ReviewState}
import frflow.decision.rules.{Command, Refusal}

/** `Deciding` over projects in memory, a key made for the run and listed as `ann`'s: who decides; `preview` records
  * nothing and gives what `decide` then records; a name the key is not listed under is refused; a decision that does
  * not count is in the view with why; and, once the model moves, what moved above a node and what accepting it acts
  * on.
  */
class DecidingSuite extends munit.CatsEffectSuite:
  private val (nonNegative, sameAbove) = (id("nonNegative"), id("sameAbove"))
  private val accept = Command.Accept(List(nonNegative, sameAbove), "it says what the service must do", Nil, Map.empty)

  test("who decides: the name given, else the name the key at hand is listed under; else no one") {
    for
      listed   <- Opened.api(Opened.before)
      unlisted <- Opened.api(Opened.before, decider = None)
      named    <- listed.deciding.developer(Some("bob"))
      key      <- listed.deciding.developer(None)
      none     <- unlisted.deciding.developer(None)
    yield assertEquals((named, key, none), (Right("bob"), Right("ann"), Left(Refusal.NoOneDecides)))
  }

  test("preview records nothing and gives what decide then records") {
    for
      api     <- Opened.api(Opened.before)
      _       <- Opened.checked(api.proving.check(None))
      seen    <- api.deciding.preview(accept, "ann")
      still   <- api.reading.view
      done    <- api.deciding.decide(accept, "ann")
      after   <- api.reading.view
    yield
      def taken(d: Either[Refusal, view.Decided]) = d.map(_.recorded.map((n, x) => (n, x.action, x.reason.text)))
      assertEquals(taken(seen), taken(done))
      assertEquals(taken(done).map(_.map(_._1)), Right(List(nonNegative, sameAbove)))
      assertEquals(still.nodes.map(_.review.standing.state).distinct, List(ReviewState.Proposed))
      assertEquals(after.nodes.map(_.review.standing.state).distinct, List(ReviewState.Accepted))
      assertEquals(after.node(sameAbove).flatMap(_.says.reason), Some("it says what the service must do"))
      assertEquals(after.node(sameAbove).flatMap(_.review.decision).map(_.action), Some(Action.Accept))
  }

  test("a name the key at hand is not listed under is refused, and nothing is recorded") {
    for
      api  <- Opened.api(Opened.before)
      out  <- api.deciding.decide(accept, "bob")
      view <- api.reading.view
    yield
      assertEquals(out, Left(Refusal.NotADecider("bob")))
      assertEquals(view.nodes.map(_.review.standing.state).distinct, List(ReviewState.Proposed))
  }

  test("a decision that does not count is in the view with why, and its node stays where it was") {
    for
      listed   <- Opened.ports()
      unlisted <- Opened.ports(decider = None)
      _        <- Opened.over(Opened.before, listed).flatMap(Opened.acceptAll)
      view     <- Opened.over(Opened.before, unlisted.copy(ledger = listed.ledger)).flatMap(_.reading.view)
    yield
      val notCounted = view.warnings.collect { case Warning.NotCounted(n, d, why) => (n, d.action, why) }
      assertEquals(notCounted, List((nonNegative, Action.Accept, Uncounted.NoDeciders),
        (sameAbove, Action.Accept, Uncounted.NoDeciders)))
      assertEquals(view.nodes.map(_.review.standing.state).distinct, List(ReviewState.Proposed))
  }

  test("once the claim's meaning moves: its part is back for what moved above it, and accepting it acts on the part") {
    for
      ports <- Opened.ports()
      _     <- Opened.over(Opened.before, ports).flatMap(Opened.acceptAll)
      after <- Opened.over(Opened.after, ports)
      view  <- after.reading.view
      diffs <- (after.reading.diff(nonNegative), after.reading.diff(sameAbove)).tupled
    yield
      val part = view.node(sameAbove).getOrElse(fail("no part"))
      assertEquals((part.review.standing.state, part.review.standing.causes), (ReviewState.Review, List(Cause.Above)))
      assertEquals(part.review.movedAbove, List(nonNegative))
      assertEquals(view.node(nonNegative).map(_.review.below), Some(List(sameAbove)))
      val (claim, below) = diffs
      val formula = claim.toList.flatMap(_.fields).filter(_.field == "formula")
      assert(formula.exists(_.lines.exists { case DiffLine.Added(_) => true; case _ => false }), formula)
      assertEquals(below.map(_.above.map(_.id)), Some(List(nonNegative)))
      assertEquals(below.map(_.above.flatMap(_.fields.map(_.field))), Some(formula.map(_.field)))
  }
