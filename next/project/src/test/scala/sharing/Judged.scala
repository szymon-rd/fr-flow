package sharing

/** What sharing's port judges (`PortSuite`): each difference from today's in where a node sits and what it assumes,
  * each node standing apart from today's, what is not proven, and today's Lean read over the port's types.
  */
object Judged:
  /** Each difference from today's sharing, with why the design makes it. */
  val differences: Map[String, (String, String)] = Map(
    "accessFollowsShares" -> ("reach, cover, permission, editPermission, inTrash, ownersShare are parts" ->
      ("today's definitions fixed the purpose's words; a definition is a claim, an equation proven of the define " +
        "giving the Definition its meaning (owner §15), a part of the purpose it is stated in (2.7)")),
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
      "delivery takes a connection from the pool and gives it back whatever happens (bracket, so guarantee); " +
      "this claim says so of its runs, both outcomes")),
    "noticesFollowChanges" -> ("deliveryGivesBack is a part" ->
      "the delivery's new claim, below the branch about notices its run serves"),
    "handleContract" -> ("assumes +oneTransactionAtATime +clockAlone" -> runs),
    "housekeepingJob" -> ("assumes +oneTransactionAtATime +clockAlone" -> runs),
    "deliveryJob" -> ("assumes +oneTransactionAtATime +mailOneAtATime +clockAlone +poolOneAtATime" -> runs))

  private def atomic(what: String) = s"runs on $what never interleave, an assumption of its model (owner §32, §36)"
  private def runs = "a claim about a program's runs rests on each model it calls being atomic (2.6); today's design " +
    "node transactions said so of the store, and the boundaries' runs were taken as steps"

  /** Where each node stands apart from today, each for a reason the design gives. */
  val standings: Map[String, List[String]] =
    // A contract is a claim (owner §15), proven of its code as today; a definition fixing a word is a claim, an
    // equation proven of the define giving the Definition its meaning, or a fixed value's (owner §15, 2.7).
    List("AcceptContract", "AccessContract", "AnnounceContract", "ApproveContract", "AskContract", "CanEditContract",
      "CanViewContract", "ChaseContract", "DeclineContract", "ForgetContract", "GoneContract", "HandleContract",
      "HousekeepingJob", "InForceContract", "InviteContract", "IsOpenContract", "MoveContract", "PendingContract",
      "RecordContract", "ReminderDueContract", "RestoreContract", "ShareContract", "TidyContract", "TransferContract",
      "TrashContract", "UnshareContract", "WarnContract", "WithdrawContract", "Cover", "EditPermission",
      "HousekeepingPeriod", "InTrash", "InvitationLifetime", "OwnersShare", "Permission", "Reach", "ReminderTime",
      "RequestLifetime", "TrashLifetime").map(_ -> List("claim", "proven", "proven", "")).toMap ++
    // Each model's runs one at a time, an assumption of the model (owner §32, §36); nothing to check of it.
    List("ClockAlone", "MailOneAtATime", "OneTransactionAtATime", "PoolOneAtATime")
      .map(_ -> List("assumption", "assumed", "", "")).toMap ++
    // That nothing but the code changes a model's state (owner §36), with the model's Scala tested against it on
    // generated runs, 200 per implementation (ModelRuns.Runs): the store, the mail server, the clock and the pool in
    // memory; today's ran its SQLite store too (1,200 runs), which is not ported (its in-memory store is).
    List("ClockKept", "LibraryKept", "MailerKept", "PoolKept").map(_ -> List("assumption", "assumed", "", "200"))
      .toMap ++
    // Delivery's runs are proven of its code, but its sends at once, branches calling the mail server that may
    // fail, are not shown to commute (commute_0): stopped on a design point (`stopped`). What rests on them waits.
    List("DeliveryJob", "DeliveryGivesBack").map(_ -> List("claim", "open", "open", "")).toMap ++
    List("NoticesFollowChanges", "AccessFollowsShares").map(_ -> List("claim", "waiting", "waiting", "")).toMap

  /** What is not proven, each for a reason: delivery's sends at once, branches calling the mail server, which may
    * fail, are not shown to commute (`commute_0`): FrFlow states it from every world, its faults included, and the
    * one list of faults the branches take in turn makes two orders differ whenever the branches fail differently
    * (one notice's sends all fail, another's do not), so the obligation is false as stated; how commutation reads
    * a failing model is a design point the step stops on (today's library stated it for a world in which no call
    * fails). What rests on delivery waits for it. And the purpose is met by doing nothing (`Idle`, the roots
    * together): today's purpose is stated over the words the code defines (canView, mayView, share, …), so a service
    * that lets nobody see or change anything meets it; what each word is, the claims below it say (crm's ruling
    * for a safety root, step 12), and sharing has no other root.
    */
  val stopped: Map[String, List[String]] = Map("deliveryJob" -> List("Check"), "deliveryGivesBack" -> List("Check"),
    "noticesFollowChanges" -> List("Check"), "accessFollowsShares" -> List("Check", "Idle"))

  /** Each value provided where the code runs, judged under owner §45 D. */
  val provided: Map[String, String] = Map(
    "events" -> ("the run's history so far, which the deadlines and the branches read as the service's moment " +
      "(atEnd): the World's under §45 D; not moved, as the deadlines rest on time passing between runs and on " +
      "housekeeping's schedule (housekeepingOnTime), which the World cannot say: its clock moves only by the " +
      "programs' sleeps, a wait outside them has no step, and an assumed rule about a state is asked cover_ of " +
      "every program (a design point); read beside no World, as today's run"),
    "startedAt" -> "when the service started: configuration, fixed for the run, the start of its history")

  /** Today's Lean over the port's types. */
  def oldOverNew(text: String): String = text
