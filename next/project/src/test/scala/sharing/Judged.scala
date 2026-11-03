package sharing

/** What sharing's port judges (`PortSuite`): each difference from today's in where a node sits and what it assumes,
  * each node standing apart from today's, what is not proven, and today's Lean read over the port's types.
  */
object Judged:
  /** Each difference from today's sharing, with why the design makes it. */
  val differences: Map[String, (String, String)] = Map(
    "accessFollowsShares" -> (("reach, cover, permission, editPermission, inTrash, ownersShare, whoMayEdit, " +
      "whatIsTrashed are parts") ->
      ("the purpose is stated over Declarations, as rooms' and auth's are (owner §14, §27, the step 13 " +
        "review's Idle ruling): may view, may edit, is in the trash; the claims at the bottom saying what each " +
        "is in terms of the code (permission, whoMayEdit, whatIsTrashed, the code standing in them, 2.7), and " +
        "the claims on the code's own words (reach, cover, editPermission, inTrash, ownersShare: equations " +
        "proven of the defines giving the Definitions the code calls their meaning, owner §15), are parts of " +
        "the purpose they are stated for")),
    "whoMayEdit" -> ("new" -> ("the purpose's \"may edit\", a Declaration, said in terms of the code: today's " +
      "permission's second word, which the code calls as its own Definition (mayEdit, editPermission)")),
    "whatIsTrashed" -> ("new" -> ("the purpose's \"is in the trash\", a Declaration, said in terms of the code: " +
      "today's inTrash, which the code calls as its own Definition (inTrash)")),
    "auditTrail" -> ("permission is a part" -> ("the branch says what a yes of viewing rests on, over the purpose's " +
      "\"may view\", a Declaration: the claim saying what it is is a part of it")),
    "editPermission" -> ("new" -> "today's permission defined two words, mayView and mayEdit: a claim per word"),
    "reminderTime" -> ("new" ->
      "today's requestLifetime defined two durations, requestLasts and remindAfter: a claim per value"),
    "invitationsAreOffers" -> ("inTrash is a part" ->
      ("inTrash is a Definition with its own code (today's was a define): the branch reads access, which reads " +
        "whether a document is in the trash, so the claim saying what inTrash is is a part of its step (2.7)")),
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
      (runs + "; " + scheduled)),
    "deliveryJob" -> ("assumes +oneTransactionAtATime +mailOneAtATime +poolOneAtATime +housekeepingOnTime" ->
      (runs + "; " + scheduled)),
    "clockKept" -> ("gone" -> ("the clock is the World's time (owner §47): nothing but its own step moves it, so " +
      "there is no assumption that nothing else does; when housekeeping last ran is a model of its own, " +
      "housekeptKept")),
    "clockNeverGoesBack" -> ("gone" -> ("time never going back is no longer trusted (owner §47): the clock's state " +
      "moves only forwards by construction, and timeMovesOn, an isConstant over the World, is proven of the world's " +
      "own step and of delivery's runs")),
    "housekeptKept" -> ("new" -> ("when housekeeping last ran is a model of its own (owner §47), which only " +
      "housekeeping changes, the onlyCodeChanges its state rests on (owner §36)")),
    "housekeptOneAtATime" -> ("new" -> atomic("when housekeeping last ran")),
    "housekeptStarts" -> ("new" -> "what housekeeping's last run is when the service starts: when it started"),
    "clockStarts" -> ("new" -> "what the time is when the service starts: when it started"),
    "libraryStarts" -> ("new" -> "what the library holds when the service starts: nothing ended at its start"),
    "timeMovesOn" -> ("new" -> ("today's clockNeverGoesBack, trusted, a claim (owner §47): a moment passed stays " +
      "passed, under the world's own step and delivery's runs (an isConstant over the World)")),
    "housekeptLately" -> ("new" -> ("a rule of the World (owner §45 D, §47): housekeeping ran no more than two " +
      "minutes ago, kept by each program and by time passing where the schedule allows; today's deadlines read " +
      "it from the history (Run.after)")),
    "nothingEndedAtHousekeeping" -> ("new" -> ("a rule of the World (owner §45 D, §47): nothing in the library had " +
      "ended when housekeeping last ran, kept by each program; today's deadlines read it from the history")),
    "logKept" -> ("new" -> ("a rule of the World (owner §45 D): every share held has its entry, every notice of a " +
      "change its entry, kept by each program; today's auditTrail and noticesFollowChanges proved it by induction " +
      "over the history")),
    "invitationsLapseOnTime" -> ("recordContract, announceContract, housekeepingJob, isOpenContract, " +
      "housekeepingOnTime no part" -> deadline),
    "trashPurgedOnTime" -> ("recordContract, announceContract, housekeepingJob, goneContract, housekeepingOnTime " +
      "no part" -> deadline),
    "requestsAnsweredOnTime" -> ("recordContract, announceContract, housekeepingJob, pendingContract, " +
      "reminderDueContract, housekeepingOnTime no part" -> deadline))

  private def scheduled = "the time a run reads is the World's, which the world moves only as housekeeping's " +
    "schedule allows (owner §47), so a claim about its runs rests on that schedule"
  private def deadline = "a deadline is a rule of the World at every moment (owner §45 D): it follows from the " +
    "World's rules (housekeptLately, nothingEndedAtHousekeeping), each kept by every program and by time passing, " +
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
    // clock, its moves where housekeeping's schedule allows; the World's rules (housekeptLately, logKept,
    // nothingEndedAtHousekeeping) each kept by every program, the code of what it calls put in, and by time passing,
    // time never going back (timeMovesOn) a claim.
    List("AcceptContract", "AccessContract", "AnnounceContract", "ApproveContract", "AskContract", "CanEditContract",
      "CanViewContract", "ChaseContract", "DeclineContract", "ForgetContract", "GoneContract", "HandleContract",
      "HousekeepingJob", "InForceContract", "InviteContract", "IsOpenContract", "MoveContract", "PendingContract",
      "RecordContract", "ReminderDueContract", "RestoreContract", "ShareContract", "TidyContract", "TransferContract",
      "TrashContract", "UnshareContract", "WarnContract", "WithdrawContract", "Cover", "EditPermission",
      "HousekeepingPeriod", "InTrash", "InvitationLifetime", "OwnersShare", "Permission", "Reach", "ReminderTime",
      "RequestLifetime", "TrashLifetime", "WhoMayEdit", "WhatIsTrashed", "DeliveryJob", "DeliveryGivesBack",
      "HousekeptLately", "LogKept", "NothingEndedAtHousekeeping", "TimeMovesOn")
      .map(_ -> List("claim", "proven", "proven", "")).toMap ++
    // Each model's runs one at a time, an assumption of the model (owner §32, §36), each model's start (its
    // `initially`), and housekeeping's schedule, a schedule of the clock restricting the world's moves of the time
    // (owner §47); nothing to check of them.
    List("MailOneAtATime", "OneTransactionAtATime", "PoolOneAtATime", "HousekeptOneAtATime", "ClockStarts",
      "HousekeptStarts", "LibraryStarts", "HousekeepingOnTime")
      .map(_ -> List("assumption", "assumed", "", "")).toMap ++
    // That nothing but the code changes a model's state (owner §36), with the model's Scala tested against it on
    // generated runs as today, from seed 1: the mail server's, the pool's and housekeeping's last run's 1,000, the
    // store's 1,200 (in memory 1,000, in SQLite 200, today's store ported), each start drawn meeting the World's
    // rules about the library (logKept); their check is the model's, not Lean's. The clock's is gone: the time is
    // the World's, moved only by its own steps (§47); its Scala is still tested against its model (1,000 runs).
    Map("LibraryKept" -> List("assumption", "assumed", "", "1200"),
      "MailerKept" -> List("assumption", "assumed", "", "1000"),
      "PoolKept" -> List("assumption", "assumed", "", "1000"),
      "HousekeptKept" -> List("assumption", "assumed", "", "1000"),
      "ClockKept" -> Nil, "ClockNeverGoesBack" -> Nil)

  /** What is not proven: nothing. Each of the World's rules is kept by every program, its `cover_` built as `impl`
    * is, the code of what the program calls put in (2.7), and by time passing; delivery's steps at once commute two
    * by two, each given its own faults (G3, the step 13 re-review's RB1 and RB2), its runs under the race's reading
    * (B1); the purpose, over its Declarations, is not met by doing nothing.
    */
  val stopped: Map[String, List[String]] = Map.empty

  /** Each value provided where the code runs, under owner §45 D: the history and now are the World's (§47). */
  val provided: Map[String, frflow.project.Ported.OnD] = Map(
    "startedAt" -> frflow.project.Ported.OnD.Configuration(
      "when the service started: fixed for the run, the start of its history"))

  /** Today's tests not ported, each deferred with why and to when (the step 13 review's S4): they need today's
    * server and scheduler (its HTTP routes, its codec, its wall-clock scheduler), which `next` does not have.
    */
  val deferred: Map[String, String] = Map(
    "the black-box oracle: 400 generated requests, waits and runs of housekeeping, on the memory store and SQLite" ->
      "needs today's server and its codec; with the server's port (step 14's documents and examples or later)",
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
      "housekeptOneAtATime", "housekeptStarts", "clockStarts", "libraryStarts", "timeMovesOn", "housekeptLately",
      "nothingEndedAtHousekeeping", "logKept").map(_ -> "new: no statement of today's to state it against").toMap ++
    List("domainTypes", "serverWiring", "transactions").map(_ -> "a design: it states nothing").toMap

  /** Today's Lean over the port's types: what today asked of each claim (its `Obl` section) read over today's run, its
    * history of events, which the port's types do not have (the run is the World's, owner §45 D, §47), so it is left
    * out, and with it housekeepingClearsOnlyTheEnded's part endedStaysEnded, today's a statement over the history.
    * The claims compared are each `claim`, which reads no history.
    */
  def oldOverNew(text: String): String =
    text.replace("import FrFlowGen.Old.EndedStaysEnded.Spec\n", "")
      .replaceAll("""(?s)\nnamespace Obl\n.*?\nend Obl\n""", "\n")
