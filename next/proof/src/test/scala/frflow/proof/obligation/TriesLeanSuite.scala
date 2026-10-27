package frflow.proof.obligation

import frflow.proof.layout.{Laid, LeanBuildSuite, LeanTag}
import frflow.proof.verdict.{Judge, ObligationStatus}

/** `Pair` built by Lean: what each try shows. `same`'s part restates it; nothing else is shown. */
class TriesLeanSuite extends LeanBuildSuite("pair", Laid(Pair.resolved, Map.empty, Nil)):
  test("pair: only the part restating `same` is shown".tag(LeanTag)) {
    val shown = judged(tries, Judge.tried).filter(_.status == ObligationStatus.Shown).map(_.name)
    assertEquals(shown, List(ObligationName.Tried(TryKind.Restates)), built)
  }
