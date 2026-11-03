package frflow.proof.layout

import frflow.proof.obligation.ObligationName

/** `Broken` built by Lean: the code that breaks what always holds is caught. `made_misdate` (a booking ending before
  * it starts) is not proven, nor `cover_fileBackwards` (one stored), nor what it hands the shelf at its call
  * (`made_fileBack_call_0`), of the claim and of the assumption alike; the pair adding two bookings at once does not
  * commute, nor do two of the adds of each element at once (two elements of a list, which may be equal); the pair
  * reading the store twice does, as do two reads of each element at once, and everything else is proven but what a
  * run over each element keeps (`cover_countEach`, `cover_putEach`): an induction over the list, the developer's.
  */
class BrokenLeanSuite extends LeanBuildSuite("broken", Laid(Broken.resolved, Map.empty, Nil),
  List("endsAfterStart", "fromOutside").flatMap(n => List(n -> ObligationName.Made("misdate"),
    n -> ObligationName.Cover("fileBackwards"), n -> ObligationName.Made("fileBack_call_0"),
    n -> ObligationName.Cover("countEach"), n -> ObligationName.Cover("putEach"))) :+
    ("putRuns" -> ObligationName.Commute(0)) :+ ("putEachRuns" -> ObligationName.Commute(0)))
