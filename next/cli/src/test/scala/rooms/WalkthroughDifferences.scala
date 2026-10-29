package rooms

/** Where the port's walk-through differs from today's (`Walkthrough.differences`), each with why. What does not
  * differ is the point: step 4's calendar fails a generated case of `grantWhenNoOverlap`, step 5's step to
  * `grantWhenFree` is refuted by a case Lean confirms, step 6 proves everything and sends the statements over moments
  * back to the developer; each check exits as today's.
  */
object WalkthroughDifferences:
  private val ends = List(
    "status bookingsEndAfterStart: - -> +" ->
      ("an assumption of always is a rule: Lean proves book keeps it, inRoom makes it and the store starts meeting " +
        "it (cover_, made_, start_; owner §27), so it is proven, not only assumed"),
    "status nothingElseWrites: none -> -" -> nothingElse,
    "status onlyBookingWrites: - -> none" ->
      "gone: the programs changing a store are derived from the code (owner §31)",
    "status tableMatchesModel: - -> none" -> tableGone)

  val judged: Map[String, List[(String, String)]] = Map(
    "base" -> ends,
    "4-code-forgets-the-next-booking" -> (ends.head :: ("status grantWhenNoOverlap: ! -> x" ->
        "status marks a failing node x before its review state (still to review), as check does") :: ends.tail),
    "5-misread-overlap" -> List(
      "check bookingsEndAfterStart: - -> +" -> ends.head._2,
      "check neverOverlap: + -> o" -> sharedLemmas,
      "check nothingElseWrites: none -> +" -> modelRuns,
      "check roomBookingsApart: + -> o" ->
        ("the port states the rule in start and end times (noOverlap, 2.3), so the misread reaches it: back-to-back " +
          "stored bookings, which the table may hold, fail the strict noOverlap, so made_inRoom cannot be proven, as " +
          "it should not; today's rule is over moments (apart), which the misread leaves alone. " + sharedLemmas),
      "status acceptWhenFree: . -> o" -> rootOpen,
      "status acceptedIsAnswered: ! -> +" -> meaningKept,
      "status answerWhenFree: . -> o" -> sharedLemmas,
      "status bookWhenFree: . -> o" -> rootOpen,
      "status bookedAfterIsStored: ! -> +" -> meaningKept,
      "status bookedIsStored: ! -> +" -> meaningKept,
      "status bookingsEndAfterStart: ! -> +" -> (ends.head._2 + "; and it is not back: " + premise),
      "status neverOverlap: + -> o" -> sharedLemmas,
      ends(1),
      ends(2),
      "status roomBookingsApart: + -> !" -> "back for review (below), and not proven (above): ! before o",
      "status storeWhenFree: . -> o" -> sharedLemmas,
      ends(3),
      "review acceptedIsAnswered: back -> kept" -> meaningKept,
      "review bookedAfterIsStored: back -> kept" -> meaningKept,
      "review bookedIsStored: back -> kept" -> meaningKept,
      "review bookingsEndAfterStart: back -> kept" -> premise,
      "review roomBookingsApart: kept -> back" ->
        "its formula moved: the port states it with noOverlap (2.3), today's with apart"),
    "6-misread-reaches-the-claim" -> List(
      "check bookingsEndAfterStart: - -> +" -> ends.head._2,
      "check nothingElseWrites: none -> +" -> modelRuns,
      "status bookingsEndAfterStart: ! -> +" -> (ends.head._2 + "; and it is not back: " + premise),
      ends(1),
      "status oneAtATime: ! -> -" -> premise,
      "status onlyBookingWrites: ! -> none" -> ends(2)._2,
      "status startsEmpty: ! -> -" -> premise,
      "status tableMatchesModel: ! -> none" -> tableGone,
      "review bookingsEndAfterStart: back -> kept" -> premise,
      "review oneAtATime: back -> kept" -> premise,
      "review onlyBookingWrites: back -> kept" -> ends(2)._2,
      "review startsEmpty: back -> kept" -> premise,
      "review tableMatchesModel: back -> kept" -> tableGone))

  private def nothingElse = "new: nothing but the code changes the table, said of the model (owner §36), " +
    "decided before the claims resting on it, the table's Scala tested against the model under it"
  private def tableGone = "gone: no store behaves as a model (owner §36); what it said of the world outside is " +
    "nothingElseWrites, and that the table does what the model does is the test of its Scala"
  private def modelRuns = "the table's Scala tested against storedBookings on 200 generated runs, as today's " +
    "tableMatchesModel said; run again since the rules the runs' states are drawn meeting changed, and said beside " +
    "the assumption that only the code writes the table"
  private def sharedLemmas = "its proof imports the shared lemmas (Proofs/Rooms/Lemmas.lean), and the lemma relating " +
    "apart to noOverlap no longer holds once noOverlap is strict: the lemmas do not build, so it is not proven (o), " +
    "said as the lemmas' failure, not its own proof's"
  private def rootOpen = "a root over Declarations is not proven while root_impl is open below a failure: o, where " +
    "today's printed . for a node whose parts fail"
  private def meaningKept = "a claim saying what a Declaration is rests on no part: the calendar's change moves only " +
    "the claims tested against it (its fingerprint governs those), and the group it shares is proven again by Lean"
  private def premise = "a premise is decided before the claims assuming it and rests on none of them, so their " +
    "change does not bring it back (today: \"a node assuming it changed\")"
