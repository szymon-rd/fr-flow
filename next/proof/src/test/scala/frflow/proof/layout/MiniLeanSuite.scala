package frflow.proof.layout

import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.{Judge, ObligationStatus}

/** Mini (`Mini`): its example is shown from the claims, and nothing else it tries. */
class MiniLeanSuite extends LeanBuildSuite("mini", MiniProject, Nil):
  test("mini: the example is shown, and no try".tag(LeanTag)) {
    val shown = judged(tries, Judge.tried).map(_._2).filter(_.status == ObligationStatus.Shown).map(_.name)
    assertEquals(shown, List(ObligationName.Example(0)), built)
  }
