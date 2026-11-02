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
  val standings: Map[String, List[String]] = Map.empty

  /** What is not proven, each for a design point the step stops on. */
  val stopped: Map[String, List[String]] = Map.empty

  /** Today's Lean over the port's types. */
  def oldOverNew(text: String): String = text
