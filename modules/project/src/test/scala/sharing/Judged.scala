package sharing

/** What sharing's port judges (`PortSuite`): each difference from today's in where a node sits and what it assumes,
  * each node standing apart from today's, what is not proven, and today's Lean read over the port's types.
  */
object Judged:
  /** Each difference from today's sharing, with why the design makes it. */
  val differences: Map[String, (String, String)] = Map(
    "whoMayEdit" -> ("new" -> ("the purpose's \"may edit\", a Declaration, said in terms of the code: today's " +
      "permission's second word, which the code calls as its own Definition (mayEdit, editPermission)")),
    "whatIsTrashed" -> ("new" -> ("the purpose's \"is in the trash\", a Declaration, said in terms of the code: " +
      "today's inTrash, which the code calls as its own Definition (inTrash)")),
    "editPermission" -> ("new" -> "today's permission defined two words, mayView and mayEdit: a claim per word"),
    "reminderTime" -> ("new" ->
      "today's requestLifetime defined two durations, requestLasts and remindAfter: a claim per value"),
    "oneTransactionAtATime" -> ("new" -> atomic("the library store")),
    "mailOneAtATime" -> ("new" -> atomic("the mail server")),
    "poolOneAtATime" -> ("new" -> atomic("the pool of connections to the mail server")),
    "poolKept" -> ("new" -> ("nothing but the service's programs changes the pool's count, the onlyCodeChanges a " +
      "model's state rests on (owner §36)")),
    "deliveryGivesBack" -> ("new" -> ("the kept combinators' use (owner §2, ARCHITECTURE 9, step 13): a run of " +
      "delivery takes a connection from the pool and gives it back whatever happens (bracket, so guarantee), even " +
      "when its sends run out of time (race); a root of its own (owner §11): no branch about notices makes it, the " +
      "pool's count saying nothing of notices (the step 13 review's S7)")),
    "handleContract" -> ("assumes +oneTransactionAtATime +housekeepingOnTime" -> (runs + "; " + scheduled)),
    "housekeepingJob" -> ("assumes +oneTransactionAtATime +housekeptOneAtATime +housekeepingOnTime" ->
      (runs + "; " + scheduled + "; " + smaller + ": what a run does to the library, the rest " +
        "housekeepingRunsCleanly")),
    "deliveryJob" -> (("failedDeliveryChangesNothing, deliveryOnlyEmptiesTheOutbox, deliveryTakesOutOnlyWhatWasSent, " +
      "deliveryTouchesOnlyWhatItSends are parts; assumes +oneTransactionAtATime +mailOneAtATime +poolOneAtATime " +
      "+housekeepingOnTime") -> (runs + "; " + scheduled + "; " + smaller)),
    "clockKept" -> ("gone" -> ("the clock is the World's time (owner §47): nothing but its own step moves it, so " +
      "there is no assumption that nothing else does; when housekeeping last ran is a model of its own, " +
      "housekeptKept")),
    "clockNeverGoesBack" -> ("gone" -> ("time never going back is no longer trusted (owner §47): the clock's state " +
      "moves only forwards by construction, and timeMovesOn, an isConstant over the World, is proven of the world's " +
      "own step and of each program's runs")),
    "housekeptKept" -> ("new" -> ("when housekeeping last ran is a model of its own (owner §47), which only " +
      "housekeeping changes, the onlyCodeChanges its state rests on (owner §36)")),
    "housekeptOneAtATime" -> ("new" -> atomic("when housekeeping last ran")),
    "housekeptStarts" -> ("new" -> "what housekeeping's last run is when the service starts: when it started"),
    "clockStarts" -> ("new" -> "what the time is when the service starts: when it started"),
    "libraryStarts" -> ("new" -> "what the library holds when the service starts: nothing ended at its start"),
    "timeMovesOn" -> ("new" -> ("today's clockNeverGoesBack, trusted, a claim (owner §47): a moment passed stays " +
      "passed, under the world's own step and each program's runs: delivery's, housekeeping's and a request's, each " +
      "looking at the clock (an isConstant over the World)")),
    "housekeptLately" -> ("new" -> ("a rule of the World (owner §45 D, §47): housekeeping ran no more than two " +
      "minutes ago, to be kept by each program and by time passing where the schedule allows; today's deadlines " +
      "read it from the history (Run.after); not proven here (stopped)")),
    "invitationsLapseOnTime" -> ("recordContract, announceContract, housekeepingJob, isOpenContract, " +
      "housekeepingOnTime no part" -> deadline),
    "trashPurgedOnTime" -> ("recordContract, announceContract, housekeepingJob, goneContract, housekeepingOnTime " +
      "no part" -> deadline),
    "requestsAnsweredOnTime" -> ("recordContract, announceContract, housekeepingJob, pendingContract, " +
      "reminderDueContract, housekeepingOnTime no part" -> deadline)) ++ JudgedParts.differences

  private def smaller = "split into smaller statements, one fact each"
  private def scheduled = "the time a run reads is the World's, which the world moves only as housekeeping's " +
    "schedule allows (owner §47), so a claim about its runs rests on that schedule"
  private def deadline = "a deadline is a rule of the World at every moment (owner §45 D): it follows from the " +
    "World's rules (housekeptLately, and the deadline's rule of what had ended by then), each kept by every program " +
    "and by time passing, " +
    "where today's followed from the history and the programs over it"
  private def atomic(what: String) = s"runs on $what never interleave, an assumption of its model (owner §32, §36)"
  private def runs = "a claim about a program's runs rests on each model it calls being atomic (2.6); today's design " +
    "node transactions said so of the store, and the boundaries' runs were taken as steps"

  /** Where each node stands apart from today, each for a reason the design gives. */
  val standings: Map[String, List[String]] =
    // A contract is a claim (owner §15), proven of its code as today; a definition fixing a word is a claim, an
    // equation proven of the define giving the Definition its meaning, or a fixed value's (owner §15, 2.7); the
    // purpose's Declarations each said by a claim at the bottom (whoMayEdit, whatIsTrashed, permission), its group
    // witnessed (`Whole.lean`); delivery's runs proven under the race's reading, its sends commuting with each
    // branch given its own faults (the step 13 review's B1 and G3), and the pool given back. The programs' runs are
    // proven on the World with time as Cats Effect models it (owner §47): the world's tick after each look at the
    // clock, its moves between runs where housekeeping's schedule allows; the World's rules (sharesLogged,
    // noticesLogged, and the four of what had ended at housekeeping's last run) each kept by every program, the code
    // of what it calls put in, and by time passing,
    // time never going back (timeMovesOn) a claim. HousekeptLately is open (stopped, below): inside a run the time
    // moves freely, so no run keeps it.
    List("AcceptContract", "AccessContract", "AnnounceContract", "ApproveContract", "AskContract", "CanEditContract",
      "CanViewContract", "ChaseContract", "DeclineContract", "ForgetContract", "GoneContract", "HandleContract",
      "HousekeepingJob", "InForceContract", "InviteContract", "IsOpenContract", "MoveContract", "PendingContract",
      "RecordContract", "ReminderDueContract", "RestoreContract", "ShareContract", "TidyContract", "TransferContract",
      "TrashContract", "UnshareContract", "WarnContract", "WithdrawContract", "Cover", "EditPermission",
      "HousekeepingPeriod", "InTrash", "InvitationLifetime", "OwnersShare", "Permission", "Reach", "ReminderTime",
      "RequestLifetime", "TrashLifetime", "WhoMayEdit", "WhatIsTrashed", "DeliveryJob", "DeliveryGivesBack",
      "TimeMovesOn")
      .map(_ -> List("claim", "proven", "proven", "")).toMap ++
    Map("HousekeptLately" -> List("claim", "open", "open", "")) ++
    // Each model's runs one at a time, an assumption of the model (owner §32, §36), each model's start (its
    // `initially`); nothing to check of them. Housekeeping's schedule, restricting the world's moves of the time
    // between runs (owner §47), stands as today's: its frozen try not shown, so it lets time pass.
    List("MailOneAtATime", "OneTransactionAtATime", "PoolOneAtATime", "HousekeptOneAtATime", "ClockStarts",
      "HousekeptStarts", "LibraryStarts")
      .map(_ -> List("assumption", "assumed", "", "")).toMap ++
    // That nothing but the code changes a model's state (owner §36), with the model's Scala tested against it on
    // generated runs as today, from seed 1: the mail server's, the pool's and housekeeping's last run's 1,000, the
    // store's 1,200 (in memory 1,000, in SQLite 200, today's store ported), each start drawn meeting the World's
    // rules about the library (sharesLogged, noticesLogged); their check is the model's, not Lean's. The clock's is
    // gone: the time is the World's, moved only by its own steps (§47); its Scala is still tested against its model
    // (1,000 runs).
    Map("LibraryKept" -> List("assumption", "assumed", "", "1200"),
      "MailerKept" -> List("assumption", "assumed", "", "1000"),
      "PoolKept" -> List("assumption", "assumed", "", "1000"),
      "HousekeptKept" -> List("assumption", "assumed", "", "1000"),
      "ClockKept" -> Nil, "ClockNeverGoesBack" -> Nil) ++ JudgedParts.standings

  /** What is not proven: housekeptLately, and each statement resting on it. Deadlines that rely on housekeeping
    * running concurrently cannot be shown when runs are read one after another: a schedule restricts only the world's
    * step between runs, and inside a run the time moves freely (the step 13d review's B1), so no program's `cover_` of
    * housekeptLately holds (a request's run may take any time while housekeeping, beside it, keeps the rule true). The
    * statements stopped with it take it as given where they start (`Reads.takes`): the four deadlines it is a part
    * of, the branches above them, and each claim about a program's runs over the World (the handling, housekeeping's
    * and delivery's claims and their parts, the pool given back, time moving on, the audit trail and its part about
    * viewing), each proven itself; and the World's other rules
    * (sharesLogged, noticesLogged, and the four of what had ended at housekeeping's last run), whose every `cover_`
    * takes it as given on the world a run starts from (`Reads.coverTakes`, the step 13d re-review's R-B1:
    * housekeeping's keeping of trashNotGoneAtHousekeeping uses
    * it), with what takes them (noticesFollowChanges). How such a rule is stated is open for the owner (ARCHITECTURE
    * 4.4, "Time"); the scheduler's tests still check it on a virtual clock (`ScheduleSuite`). Each other rule's
    * `cover_`s are proven of every program, each built as `impl` is, the code of what the program calls put in (2.7),
    * and of time passing; delivery's steps at once commute two by two, each given its own faults (G3, the step 13
    * re-review's RB1 and RB2), its runs under the race's reading (B1); the purpose, over its Declarations, is not met
    * by doing nothing.
    */
  val stopped: Map[String, List[String]] =
    val concurrent = "Kept(housekeptLately)"
    Map("housekeptLately" -> List("Check", concurrent)) ++
      List("trashPurgedOnTime", "invitationsLapseOnTime", "requestsAnsweredOnTime", "remindersOnTime",
        "trashUntilGone", "invitationsAreOffers", "accessRequestsAreAsks", "auditTrail", "viewingRestsOnTheLog",
        "noticesFollowChanges", "handleContract", "housekeepingJob", "housekeepingRunsCleanly",
        "failedHousekeepingChangesNothing", "housekeepingNotesItsRun", "housekeepingSendsNoMail", "deliveryJob",
        "failedDeliveryChangesNothing", "deliveryOnlyEmptiesTheOutbox", "deliveryTakesOutOnlyWhatWasSent",
        "deliveryTouchesOnlyWhatItSends", "deliveryGivesBack", "timeMovesOn", "sharesLogged", "noticesLogged",
        "trashNotGoneAtHousekeeping", "invitationsOpenAtHousekeeping", "requestsPendingAtHousekeeping",
        "remindedAtHousekeeping").map(_ -> List(concurrent)).toMap

  /** Each value provided where the code runs, under owner §45 D: the history and now are the World's (§47). */
  val provided: Map[String, frflow.project.Ported.OnD] = Map(
    "startedAt" -> frflow.project.Ported.OnD.Configuration(
      "when the service started: fixed for the run, the start of its history"))

  /** Today's tests not ported, each deferred with why and to when (the step 13 review's S4): they need today's
    * server and scheduler (its HTTP routes, its codec, its wall-clock scheduler), which the port does not have. Step
    * 14 deleted today's example; its server is at f727b4a (examples/sharing/src/main/scala/sharing/http), and its
    * tests wait for the server's port, carried past step 14 (rebuild-carry.md).
    */
  val deferred: Map[String, String] = Map(
    "the black-box oracle: 400 generated requests, waits and runs of housekeeping, on the memory store and SQLite" ->
      "needs today's server and its codec; with the server's port, after step 14",
    "many clients at once: serializable results in commit order, every notice delivered once or waiting" ->
      ("needs today's server; the transactions and the delivery's interleavings are tested on the models " +
        "(InterleavingsSuite) and proven (commute_0 to commute_6); with the server's port"),
    "a scripted session: reminded and declined, retried and delivered once, a 503 changing nothing, a yes explained" ->
      ("needs today's server and its routes; its pieces run in production's interpreter here (SeededSuite); with " +
        "the server's port"),
    "the codec: routes read, refused with a reason, no other route" -> "today's server's own; with the server's port",
    "the server's own answers: 400 with the reason, 404, 503 past the time limit, 500 on an internal error" ->
      "today's server's own; with the server's port")

  /** Each node not stated against today's in `Port.lean`, with why (the step 13 review's S1). */
  val unstated: Map[String, String] =
    val run = "today's statement reads today's run (`Run.after`), of today's programs over today's boundaries' " +
      "world (`Boundaries.lean`, its clock a record of its own, `ClockState`), which the port's types do not have; " +
      "the port's reads the history's last moment (`atEnd`) and the code"
    List("accessRequestsAreAsks", "auditTrail", "endedStaysEnded", "housekeepingOnTime", "invitationsAreOffers",
      "invitationsLapseOnTime", "noticesFollowChanges", "requestsAnsweredOnTime", "trashPurgedOnTime",
      "trashUntilGone").map(_ -> run).toMap ++
    List("deliveryJob", "handleContract", "housekeepingJob").map(_ -> ("today's program is stated over today's " +
      "boundaries' world, which the port's types do not have; the port's over the models' World (owner §36)")).toMap ++
    Map("accessFollowsShares" -> ("today's purpose's module imports today's programs over today's boundaries' " +
      "world, so it is not built over the port's types; the port's states it over the Declarations, each of which " +
      "today's word meets the port's claim of (`permission_today`, `whoMayEdit_today`, `whatIsTrashed_today`)")) ++
    List("libraryKept", "mailerKept").map(_ -> ("today's assumption is of a boundary's model in " +
      "today's world; the port's of the model's state in the World (owner §36)")).toMap ++
    List("oneTransactionAtATime", "mailOneAtATime", "poolOneAtATime", "poolKept", "deliveryGivesBack", "housekeptKept",
      "housekeptOneAtATime", "housekeptStarts", "clockStarts", "libraryStarts", "timeMovesOn", "housekeptLately")
      .map(_ -> "new: no statement of today's to state it against").toMap ++
    List("domainTypes", "serverWiring", "jobsWiring", "transactions").map(_ -> "a design: it states nothing").toMap ++
    JudgedParts.unstated

  /** Today's Lean over the port's types: what today asked of each claim (its `Obl` section) read over today's run, its
    * history of events, which the port's types do not have (the run is the World's, owner §45 D, §47), so it is left
    * out, and with it housekeepingClearsOnlyTheEnded's part endedStaysEnded, today's a statement over the history.
    * The claims compared are each `claim`, which reads no history.
    */
  def oldOverNew(text: String): String =
    text.replace("import FrFlowGen.Old.EndedStaysEnded.Spec\n", "")
      .replaceAll("""(?s)\nnamespace Obl\n.*?\nend Obl\n""", "\n")
