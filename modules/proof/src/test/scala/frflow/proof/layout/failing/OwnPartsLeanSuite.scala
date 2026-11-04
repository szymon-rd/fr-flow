package frflow.proof.layout.failing

import frflow.proof.layout.{Laid, LeanBuildSuite}
import frflow.proof.obligation.ObligationName

/** `OwnParts` built by Lean: `totalTwo` is proven of `sumOf` from its part about `total` itself, the code put in it,
  * while that part, which needs an induction, is left open: the part is what the proof uses. Two false siblings about
  * the same code are each left open: neither is given the other.
  */
class OwnPartsLeanSuite extends LeanBuildSuite("ownparts", Laid(OwnParts.resolved, Map.empty, Nil),
  List("totalCons", "fAbove", "fAboveToo").map(_ -> ObligationName.Impl))
