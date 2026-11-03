package frflow.project.assumed

import frflow.core.checking.{Assumed, Checking, Shown}
import frflow.core.name.{NodeId, SymbolName}
import frflow.eval.assumed.Lookup
import frflow.project.pipeline.Texts
import whole.Theories

/** An assumption about an operation known only by assumptions that its model's generated runs cannot evaluate (the
  * step 13c review's S3): trusted, not tested, and said so where its checks are shown (`show`) and in its row
  * (`check`); `status` warns of it (the API's `ReadingSuite`). Two lookups of equal numbers answering alike are two
  * runs of `has` in one statement, which no run of it reads.
  */
class UntestedSuite extends munit.FunSuite:
  private val t = Theories.theory(Lookup.alike)
  private val (alike, answers) = (NodeId("hasAlike"), NodeId("hasAnswers"))
  private val has = SymbolName("has")

  test("an assumption the runs cannot evaluate is trusted, not tested; one they read as a run of has is tested") {
    assertEquals(Assumed.untested(t, alike), List(has))
    assertEquals(Assumed.untested(t, answers), Nil)
    assertEquals(Shown.of(t, alike).assumed, List(Assumed.Untested(List(has))))
    assertEquals(Shown.of(t, answers).assumed, List(Assumed.Assumption))
  }

  test("show says it: trusted, not tested") {
    assert(Checking.of(t, alike).contains(Checking.TrustedUntested(List(has))), Checking.of(t, alike))
    assert(!Checking.of(t, answers).exists { case Checking.TrustedUntested(_) => true; case _ => false })
    assert(Texts.checking(t, alike).exists(_.startsWith("trusted, not tested")), Texts.checking(t, alike))
  }

  test("check's row says it: trusted, not tested") {
    assertEquals(frflow.wire.snapshot.Rows.code(Shown.of(t, alike)).assumed, List("trusted, not tested"))
    assertEquals(frflow.wire.snapshot.Rows.code(Shown.of(t, answers)).assumed, List("assumption"))
  }
