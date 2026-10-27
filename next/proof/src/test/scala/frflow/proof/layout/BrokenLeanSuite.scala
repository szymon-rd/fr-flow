package frflow.proof.layout

import frflow.proof.obligation.ObligationName

/** `Broken` built by Lean: the code that breaks what always holds is caught. `made_misdate` (a booking ending before
  * it starts) is not proven, nor `cover_fileBackwards` (one stored), of the claim and of the assumption alike; the
  * pair adding two bookings at once does not commute; the pair reading the store twice does, and everything else is
  * proven.
  */
class BrokenLeanSuite extends LeanBuildSuite("broken", Laid(Broken.resolved, Map.empty, Nil),
  List("endsAfterStart", "fromOutside").flatMap(n =>
    List(n -> ObligationName.Made("misdate"), n -> ObligationName.Cover("fileBackwards"))) :+
    ("putRuns" -> ObligationName.Commute(0)))
