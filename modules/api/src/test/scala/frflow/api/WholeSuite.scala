package frflow.api

import frflow.api.fixture.{Opened, Shelf}
import frflow.api.node.lean.{ObligationState, ObligationView}
import frflow.api.view.whole.{ExampleOutcome, ExampleView, OnClaims}
import frflow.eval.run.OnCode

/** The theory as a whole in the view, each obligation with Rocq's outcome and messages: the states each store starts
  * in (rooms has two), the consistency groups, what is shown possible, and the examples, which pass when the code
  * holds them and Rocq shows them, fail when it does not or the claims contradict them, and are reported apart when
  * the claims do not decide them.
  */
class WholeSuite extends munit.CatsEffectSuite:
  test("each consistency group and each thing shown possible carries Rocq's outcome of its theorem") {
    Opened.api(Opened.rooms).flatMap(api => Opened.checked(api.proving.check(None))).map { v =>
      assert(v.whole.groups.forall(_.check.theorem.startsWith("consistent_")), v.whole)
      assert(v.whole.possible.forall((_, c) => c.state != ObligationState.Unchecked), v.whole.possible)
    }
  }

  test("an example passes when the code holds it and Rocq shows it; the claims not deciding it, it is reported " +
    "apart, no failure; the claims contradicting it (its opposite shown), it fails") {
    val examples = Shelf.BeforeExamples().elaborated.fold(e => fail(e.toString), identity)
    val project = Opened.project(Shelf.Before.kb, examples)
    def checked(shown: String*) = Opened.api(project, rocq = Rocq.Proving(Set.empty, shown.toSet))
      .flatMap(api => Opened.checked(api.proving.check(None)))
    for
      undecided    <- checked()
      shown        <- checked("example_BeforeExamples_0")
      contradicted <- checked("example_BeforeExamples_0_opposite")
    yield
      val example = shown.whole.examples.headOption.getOrElse(fail("no example"))
      assertEquals(example.onCode, OnCode.Holds)
      assert(example.onClaims match { case OnClaims.Rocq(c, _) => c.state == ObligationState.Shown; case _ => false })
      assertEquals(List(shown, undecided, contradicted).map(_.whole.examples.map(_.outcome)),
        List(List(ExampleOutcome.Passes), List(ExampleOutcome.Undecided), List(ExampleOutcome.Fails)))
      assertEquals((shown.overview.examples(ExampleOutcome.Passes),
        undecided.overview.examples(ExampleOutcome.Undecided), contradicted.overview.examples(ExampleOutcome.Fails)),
        (1, 1, 1))
  }

  test("an example shown both ways says the claims are inconsistent there, and fails; a fact only about " +
    "Declarations the claims give passes; one that also sets values, which nothing checks, is not decided") {
    def lean(state: ObligationState) = ObligationView("t", state, Nil)
    val both = ExampleView("both", OnClaims.Rocq(lean(ObligationState.Shown), lean(ObligationState.Shown)),
      OnCode.Holds)
    val abstractShown = ExampleView("only Declarations", OnClaims.Rocq(lean(ObligationState.Shown),
      lean(ObligationState.NotShown)), OnCode.Abstract(Nil))
    val abstractOpen = abstractShown.copy(onClaims = OnClaims.Rocq(lean(ObligationState.NotShown),
      lean(ObligationState.NotShown)))
    assert(both.onClaims.inconsistent && !abstractShown.onClaims.inconsistent)
    val abstractGiven = abstractShown.copy(onClaims = OnClaims.ScalaOnly)
    val valued = abstractGiven.copy(onCode = OnCode.Holds)
    assertEquals(List(both, abstractShown, abstractOpen, abstractGiven, valued).map(_.outcome),
      List(ExampleOutcome.Fails, ExampleOutcome.Passes, ExampleOutcome.Undecided, ExampleOutcome.Undecided,
        ExampleOutcome.Passes))
  }
