package frflow.proof.layout

import frflow.proof.obligation.{ObligationName, TryKind}
import frflow.proof.verdict.{Judge, ObligationStatus}

/** Mini (`Mini`): its example is shown from the claims, and of what else it tries only that `bookRuns`, whose post is
  * `True`, says nothing (the tautology try of a claim with no parts, `vacuous`).
  */
class MiniLeanSuite extends LeanBuildSuite("mini", MiniProject, Nil):
  test("mini: the example is shown, and of the tries only bookRuns' tautology".tag(LeanTag)) {
    val shown = judged(tries, Judge.tried).filter(_._2.status == ObligationStatus.Shown).map((m, r) => m -> r.name)
    assertEquals(shown.map(_._2), List(ObligationName.Tried(TryKind.Vacuous), ObligationName.Example("Mini", 0)), built)
    assert(shown.headOption.exists(_._1.contains("bookRuns")), shown)
  }
