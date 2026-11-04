package frflow.api

import frflow.api.node.lean.ObligationState
import frflow.api.view.Warning
import frflow.api.view.whole.OnClaims
import frflow.eval.run.OnCode

/** The theory as a whole in the view, each obligation with Lean's outcome and messages: the states each store starts
  * in (rooms has two), the consistency groups, what is shown possible, and the examples, which pass when the code
  * holds them and Lean shows them.
  */
class WholeSuite extends munit.CatsEffectSuite:
  test("a start Lean does not prove is in the view with Lean's messages, warned of, and the project is not complete") {
    for
      proven <- Opened.api(Opened.rooms).flatMap(api => Opened.checked(api.proving.check(None)))
      first   = proven.whole.starts.headOption.getOrElse(fail("rooms has no start"))
      failed <- Opened.api(Opened.rooms, lean = Lean.Proving(Set(first.check.theorem), Set.empty))
                  .flatMap(api => Opened.checked(api.proving.check(None)))
    yield
      assertEquals(proven.whole.starts.map(_.check.state).distinct, List(ObligationState.Proven))
      assert(first.check.theorem.startsWith("start_"), first)
      assertEquals(proven.warnings.collect { case w: Warning.StartNotProven => w }, Nil)
      val start = failed.whole.starts.find(_.statement == first.statement).getOrElse(fail("no start"))
      assertNotEquals(start.check.state, ObligationState.Proven)
      assert(start.check.messages.exists(_.error), start.check)
      assert(failed.warnings.contains(Warning.StartNotProven(first.statement)), failed.warnings)
      assert(!failed.overview.complete)
  }

  test("each consistency group and each thing shown possible carries Lean's outcome of its theorem") {
    Opened.api(Opened.rooms).flatMap(api => Opened.checked(api.proving.check(None))).map { v =>
      assert(v.whole.groups.nonEmpty && v.whole.groups.forall(_.check.theorem.startsWith("consistent_")), v.whole)
      assert(v.whole.possible.forall((_, c) => c.state != ObligationState.Unchecked), v.whole.possible)
    }
  }

  test("an example passes when the code holds it and Lean shows it; not shown, it does not") {
    val examples = Shelf.BeforeExamples().elaborated.fold(e => fail(e.toString), identity)
    val project = Opened.project(Shelf.Before.kb, examples)
    for
      notShown <- Opened.api(project).flatMap(api => Opened.checked(api.proving.check(None)))
      shown    <- Opened.api(project, lean = Lean.Proving(Set.empty, Set("example_0")))
                    .flatMap(api => Opened.checked(api.proving.check(None)))
    yield
      val example = shown.whole.examples.headOption.getOrElse(fail("no example"))
      assertEquals(example.onCode, OnCode.Holds)
      assert(example.onClaims match { case OnClaims.Lean(c) => c.state == ObligationState.Shown; case _ => false })
      assertEquals((shown.overview.examples(true), notShown.overview.examples(false)), (1, 1))
  }
