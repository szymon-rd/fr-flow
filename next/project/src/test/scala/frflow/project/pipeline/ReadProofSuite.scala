package frflow.project.pipeline

import frflow.core.name.NodeId
import frflow.decision.review.Unproven
import frflow.eval.EvalError
import frflow.project.Projects
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.*
import frflow.testing.Seed
import frflow.testing.report.*
import java.time.Instant

/** What of a node is not proven again, as decisions read it: only current checks and reports count; Lean proves its
  * code only when an `impl` (or `root_impl`) is asked and proven; a report not checked (no Scala value) is no failing
  * test, but a shortfall of cases on a checked one is.
  */
class ReadProofSuite extends munit.FunSuite:
  private val a = Projects.bare(Projects.rooms)
  private val (book, grant) = (NodeId("bookWhenFree"), NodeId("grantWhenNoOverlap"))

  private def checked(id: NodeId, key: CheckKey, results: Result*): Analysis =
    a.withRecorded(Recorded(Checks(Map(id -> NodeCheck(id, key, CheckStatus.Proven, results.toList, Nil,
      Instant.EPOCH)), None), Map.empty, Map.empty))
  private def reported(count: Count, outcome: Outcome): Analysis =
    a.withRecorded(Recorded(Checks.none, Map(grant -> (TestKeys.of(a, grant), TestReport(count, Seed(1),
      Against.Claim(grant), outcome, Nil, Nil))), Map.empty))
  private def standing(on: Analysis, id: NodeId) = on.subjects.get(id).map(_.proof).getOrElse(fail(id.value))

  test("what is not proven of a leaf: its check, nothing below it") {
    val open = standing(a, grant).unproven
    assert(open.contains(Unproven.Check) && open.contains(Unproven.NothingBelow), open)
  }

  test("its code is proven when its impl is asked and proven; open, it is not, and said so") {
    val proven = checked(book, a.keys.node(book), Result(ObligationName.Impl, ObligationStatus.Proven, Nil))
    val open = checked(book, a.keys.node(book), Result(ObligationName.Impl, ObligationStatus.Open, Nil))
    assert(standing(proven, book).codeProven)
    assert(!standing(open, book).codeProven)
    assert(standing(open, book).unproven.contains(Unproven.Implementation))
    assert(!standing(a, grant).codeProven)
  }

  test("a check whose key moved proves nothing") {
    val stale = checked(book, CheckKey("moved"), Result(ObligationName.Impl, ObligationStatus.Proven, Nil))
    assert(!standing(stale, book).codeProven)
    assert(standing(stale, book).unproven.contains(Unproven.Check))
  }

  test("a report not checked is no failing test; a checked one short of cases is; with none, it is not tested yet") {
    def tests(on: Analysis) = standing(on, grant).unproven.contains(Unproven.Tests)
    assert(!tests(reported(Count(200, 4), Outcome.NotChecked(EvalError.Quantified))))
    assert(tests(reported(Count(200, 198), Outcome.Passed)))
    assert(!tests(reported(Count(200, 200), Outcome.Passed)))
    assert(!tests(a) && standing(a, grant).unproven.contains(Unproven.NotTested))
  }
