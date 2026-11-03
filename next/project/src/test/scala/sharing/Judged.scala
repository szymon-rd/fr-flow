package sharing

/** What sharing's port judges (`PortSuite`): each difference from today's in where a node sits and what it assumes,
  * each node standing apart from today's, what is not proven, and today's Lean read over the port's types.
  */
object Judged:
  /** Each difference from today's sharing, with why the design makes it. */
  val differences: Map[String, (String, String)] = Map(
    "accessFollowsShares" -> (("reach, cover, permission, editPermission, inTrash, ownersShare, whoMayEdit, " +
      "whatIsTrashed are parts") ->
      ("the purpose is stated over Declarations, as rooms' and auth's are (owner §14, §27, the step 13 review's Idle " +
        "ruling): may view, may edit, is in the trash; the claims at the bottom saying what each is in terms of the " +
        "code (permission, whoMayEdit, whatIsTrashed, the code standing in them, 2.7), and the claims on the code's " +
        "own words (reach, cover, editPermission, inTrash, ownersShare: equations proven of the defines giving the " +
        "Definitions the code calls their meaning, owner §15), are parts of the purpose they are stated for")),
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
    "clockAlone" -> ("new" -> atomic("the clock")),
    "poolOneAtATime" -> ("new" -> atomic("the pool of connections to the mail server")),
    "poolKept" -> ("new" -> ("nothing but the service's programs changes the pool's count, the onlyCodeChanges a " +
      "model's state rests on (owner §36)")),
    "deliveryGivesBack" -> ("new" -> ("the kept combinators' use (owner §2, ARCHITECTURE 9, step 13): a run of " +
      "delivery takes a connection from the pool and gives it back whatever happens (bracket, so guarantee), even " +
      "when its sends run out of time (race); a root of its own (owner §11): no branch about notices makes it, the " +
      "pool's count saying nothing of notices (the step 13 review's S7)")),
    "handleContract" -> ("assumes +oneTransactionAtATime +clockAlone" -> runs),
    "housekeepingJob" -> ("assumes +oneTransactionAtATime +clockAlone" -> runs),
    "deliveryJob" -> ("assumes +oneTransactionAtATime +mailOneAtATime +clockAlone +poolOneAtATime" -> runs))

  private def atomic(what: String) = s"runs on $what never interleave, an assumption of its model (owner §32, §36)"
  private def runs = "a claim about a program's runs rests on each model it calls being atomic (2.6); today's design " +
    "node transactions said so of the store, and the boundaries' runs were taken as steps"

  /** Where each node stands apart from today, each for a reason the design gives. */
  val standings: Map[String, List[String]] =
    // A contract is a claim (owner §15), proven of its code as today; a definition fixing a word is a claim, an
    // equation proven of the define giving the Definition its meaning, or a fixed value's (owner §15, 2.7); the
    // purpose's Declarations each said by a claim at the bottom (whoMayEdit, whatIsTrashed, permission), its group
    // witnessed (`Whole.lean`); delivery's runs proven under the race's reading, its sends commuting with each
    // branch given its own faults (the step 13 review's B1 and G3), and the pool given back.
    List("AcceptContract", "AccessContract", "AnnounceContract", "ApproveContract", "AskContract", "CanEditContract",
      "CanViewContract", "ChaseContract", "DeclineContract", "ForgetContract", "GoneContract", "HandleContract",
      "HousekeepingJob", "InForceContract", "InviteContract", "IsOpenContract", "MoveContract", "PendingContract",
      "RecordContract", "ReminderDueContract", "RestoreContract", "ShareContract", "TidyContract", "TransferContract",
      "TrashContract", "UnshareContract", "WarnContract", "WithdrawContract", "Cover", "EditPermission",
      "HousekeepingPeriod", "InTrash", "InvitationLifetime", "OwnersShare", "Permission", "Reach", "ReminderTime",
      "RequestLifetime", "TrashLifetime", "WhoMayEdit", "WhatIsTrashed", "DeliveryJob", "DeliveryGivesBack")
      .map(_ -> List("claim", "proven", "proven", "")).toMap ++
    // Each model's runs one at a time, an assumption of the model (owner §32, §36); nothing to check of it.
    List("ClockAlone", "MailOneAtATime", "OneTransactionAtATime", "PoolOneAtATime")
      .map(_ -> List("assumption", "assumed", "", "")).toMap ++
    // That nothing but the code changes a model's state (owner §36), with the model's Scala tested against it on
    // generated runs as today, from seed 1: the clock's and the mail server's 1,000, the store's 1,200 (in memory
    // 1,000, in SQLite 200, today's store ported), the pool's 1,000; their check is the model's, not Lean's.
    Map("ClockKept" -> List("assumption", "assumed", "", "1000"), "LibraryKept" ->
      List("assumption", "assumed", "", "1200"), "MailerKept" -> List("assumption", "assumed", "", "1000"),
      "PoolKept" -> List("assumption", "assumed", "", "1000"))

  /** What is not proven: nothing. Delivery's steps at once commute two by two, each given its own faults (G3,
    * the step 13 re-review's RB1 and RB2), and its runs are proven under the race's reading (B1); the purpose, over
    * its Declarations, is not met by doing nothing (the idle try fails: what the Declarations are, the claims at the
    * bottom say in terms of the code).
    */
  val stopped: Map[String, List[String]] = Map.empty

  /** Each value provided where the code runs, under owner §45 D. */
  val provided: Map[String, frflow.project.Ported.OnD] = Map(
    "events" -> frflow.project.Ported.OnD.Stopped("G1", "the run's history so far, which the deadlines and the " +
      "branches read as the service's moment (atEnd): the World's under §45 D, not moved: the deadlines rest on time " +
      "passing between runs and on housekeeping's schedule (housekeepingOnTime), which the World cannot say (its " +
      "clock moves only by the programs' sleeps, a wait outside them has no step, and an assumed rule about a state " +
      "is asked cover_ of every program): waits for the owner (G1, an outside step of the clock)"),
    "startedAt" -> frflow.project.Ported.OnD.Configuration(
      "when the service started: fixed for the run, the start of its history"))

  /** Today's tests not ported, each deferred with why and to when (the step 13 review's S4): they need today's
    * server and scheduler (its HTTP routes, its codec, its wall-clock scheduler), which `next` does not have.
    */
  val deferred: Map[String, String] = Map(
    "the scheduler: runs keeping to its assumption meet every deadline; adversarial delays break housekeepingOnTime" ->
      ("the evidence for housekeepingOnTime, kept as an assumption: needs today's scheduler on a fake clock, and " +
        "time passing between runs in the World (G1); with G1's outside step, or the server, whichever comes first"),
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
    List("clockKept", "libraryKept", "mailerKept").map(_ -> ("today's assumption is of a boundary's model in " +
      "today's world; the port's of the model's state in the World (owner §36)")).toMap ++
    List("oneTransactionAtATime", "mailOneAtATime", "clockAlone", "poolOneAtATime", "poolKept", "deliveryGivesBack")
      .map(_ -> "new: no statement of today's to state it against").toMap ++
    List("domainTypes", "serverWiring", "transactions").map(_ -> "a design: it states nothing").toMap

  /** Today's Lean over the port's types. */
  def oldOverNew(text: String): String = text
