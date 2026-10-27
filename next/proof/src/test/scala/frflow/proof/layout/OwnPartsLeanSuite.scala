package frflow.proof.layout

import frflow.proof.obligation.ObligationName

/** `OwnParts` built by Lean: `totalTwo` is proven of `sumOf` from its part about `total` itself, the code put in it,
  * while that part, which needs an induction, is left open: the part is what the proof uses.
  */
class OwnPartsLeanSuite extends LeanBuildSuite("ownparts", Laid(OwnParts.resolved, Map.empty, Nil),
  List("totalCons" -> ObligationName.Impl))
