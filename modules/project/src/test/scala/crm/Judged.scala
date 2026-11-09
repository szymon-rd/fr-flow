package crm

/** What crm's port judges (`PortSuite`): each difference from today's in where a node sits and what it assumes, each
  * node standing apart from today's, how each value provided where the code ran stands under owner §45 D, and what is
  * not proven (nothing).
  */
object Judged:
  /** Each difference from today's crm, with why the design makes it. */
  val differences: Map[String, (String, String)] = Map(
    "addedIsFound" -> ("new" -> "today's first general expectation of the root, a root of its own (owner §22)"),
    "writesLeaveOthers" -> ("new" -> "today's second general expectation of the root, a root of its own (owner §22)"),
    "searchesAsk" -> ("new" -> "today's searches defined two words, finds and asksFor: a claim per word (2.7)"),
    "ownership" -> ("new" -> "today's companies defined two words, companyOf and owner: a claim per word (2.7)"),
    "keyedTables" -> ("new" -> ("the tables hold one row per key (owner §40): what the stores from outside meet, " +
      "the assumption of always[CrmStore] the claim needs (2.6)")),
    "oneRowPerKey" -> ("new" -> "the claim of always[CrmStore] owner §40 asks: every store the CRM makes meets it"),
    "tablesStartEmpty" -> ("new" -> ("what the database starts with, which a rule of its state rests on (2.6, " +
      "Problem.NoStart)")),
    "runsOneAtATime" -> ("new" -> "runs on the database never interleave, an assumption of the model (owner §32)"),
    "searchKeeps" -> ("new" -> ("what the database's search leaves, known only by what is assumed of it (G2): " +
      "nothing changed; the database's rules need it (Problem.LeavesUnsaid)")),
    "storeEdits" -> ("gone" -> ("storing the rows about a record is the database model's operation now, its " +
      "meaning the model's (storeAbout.means), its Scala tested against it, the write side a program over it")),
    "crmRun" -> ("assumes +tablesModel +runsOneAtATime +tablesStartEmpty +keyedTables" ->
      ("today's definition over a provided store and history is a rule of the database's state, the World's " +
        "(owner §45 D), proven of the code that changes it (cover_): it rests on what the database starts with, " +
        "nothing but the code changing it, and its runs one at a time (2.6); and " + keyed)),
    "sharedCrm" -> (("companies, ownership, searches, searchesAsk, readers, adding, sharing are parts; assumes " +
      "+keyedTables") -> (words + "; may read is a word of its own, readable, which readers says, so that the root " +
        "reads as one condition per word; and " + keyed + ", the words read in the World (searches reads the " +
        "screens' runs)")),
    "readers" -> ("new" -> ("what readable is: the user's company's record, or one shared with it now; today's root " +
      "stated it inline (Port.lean, sharedCrm)")),
    "storeMirrorsRequests" -> (("recordsMirrorAdds, sharesMirrorGrants are parts; writesTakeEffect, " +
      "writesOnlyAsAsked, recordsKept, sharesExpire no part; assumes +keyedTables") ->
      (splitInto("recordsMirrorAdds, sharesMirrorGrants") + "; today's parts are theirs now. And " + keyed)),
    "visibility" -> ("readContract, dealSearch are parts; noCrossTenantRead no part; assumes +keyedTables " +
      "+runsOneAtATime" -> ("noCrossTenantRead is a root (owner §40); today's searchesMatch, gone, said only what " +
        "visibility says, so the screens' contracts are its parts. And " + runs)),
    "noCrossTenantRead" -> ("readsOnlyReadable, dealsOnlyReadable are parts; readContract, dealSearch no part; " +
      "assumes +keyedTables +runsOneAtATime" -> ("its parts are the screens' parts it rests on, one per screen, its " +
        "formula their conjunction; and " + runs)),
    "readContract" -> ("readsOnlyMatching, readsOnlyReadable, readsAllReadable are parts; assumes +keyedTables " +
      "+runsOneAtATime" -> (splitInto("readsOnlyMatching, readsOnlyReadable, readsAllReadable") + "; and " + runs)),
    "dealSearch" -> ("dealsOnlyMatching, dealsOnlyDeals, dealsOnlyReadable, dealsAllReadable are parts; assumes " +
      "+keyedTables +runsOneAtATime" -> (splitInto("dealsOnlyMatching, dealsOnlyDeals, dealsOnlyReadable, " +
        "dealsAllReadable") + "; and " + runs)),
    "writeContract" -> ("writeKeepsRecords, writeKeepsOthers, writeDoesAsked, writeOnlyAsked are parts; assumes " +
      "+keyedTables" -> (splitInto("writeKeepsRecords, writeKeepsOthers, writeDoesAsked, writeOnlyAsked") + "; and " +
        keyed)),
    "sharesExpire" -> ("expiryKeepsRecords, expiryKeepsLiveShares, expiryKeepsLiveTimes are parts; assumes " +
      "+keyedTables" -> (splitInto("expiryKeepsRecords, expiryKeepsLiveShares, expiryKeepsLiveTimes") + "; and " +
        keyed)),
    "searchesMatch" -> ("gone" -> ("its two directions are what visibility, its parent, says (the first without " +
      "the user's access), so it is dropped as literally implied (resources/crm/port/Port.lean, searchesMatch)")),
    "recordsByQuery" -> ("gone" -> (splitInto("fetchesOnlyMatches, fetchesEveryMatch") + ", two assumptions, as an " +
      "assumption is never a parent; together today's (resources/crm/port/Port.lean, recordsByQuery)")),
    "saveWrite" -> ("gone" -> (splitInto("saveStores, saveLogs, saveReturns") + "; the parent only restated its " +
      "parts, so they stand alone. The write side is a program over the database now (owner §45 D): each part says " +
      "what a run leaves or gives, which rests on the database's runs being one at a time (2.6)")),
    "expiryJob" -> ("gone" -> (splitInto("jobStoresExpired, jobLogsRun, jobReturnsExpired") + "; the parent only " +
      "restated its parts, so they stand alone, each about the job's runs, which rest on the database's runs being " +
      "one at a time (2.6)")),
    "expirySchedule" -> ("new" -> "today's expiryJobWiring stated three decisions: the job's schedule is one of them"),
    "databaseLock" -> ("new" -> ("today's expiryJobWiring and writeSideWiring each stated the database's lock: one " +
      "design for every program"))) ++
    newParts.map(_ -> ("new" -> "a part of a node today bundling several facts (see that node's difference)")) ++
    List("writesTakeEffect", "writesOnlyAsAsked", "recordsKept").map(_ -> ("assumes +keyedTables" -> keyed))


  /** The parts the nodes bundling several facts are split into (one idea per node). */
  def newParts: List[String] = List("recordsMirrorAdds", "sharesMirrorGrants", "fetchesOnlyMatches",
    "fetchesEveryMatch", "readsOnlyMatching", "readsOnlyReadable", "readsAllReadable", "dealsOnlyMatching",
    "dealsOnlyDeals", "dealsOnlyReadable", "dealsAllReadable", "writeKeepsRecords", "writeKeepsOthers",
    "writeDoesAsked", "writeOnlyAsked", "saveStores", "saveLogs", "saveReturns", "expiryKeepsRecords",
    "expiryKeepsLiveShares", "expiryKeepsLiveTimes", "jobStoresExpired", "jobLogsRun", "jobReturnsExpired")

  private def splitInto(parts: String) = s"split into parts: $parts, each one fact of today's node, which is their " +
    "conjunction (Port.lean: today's claim is the port's, or theirs together)"

  private def words = "today's definitions of the purpose's words are claims saying what each Declaration is, " +
    "parts of the purpose they are stated in (2.7)"
  private def keyed = "its Lean takes what always holds of every store, the tables' one row per key, which values " +
    "from outside meet by keyedTables (2.6, owner §40)"
  private def runs = "a screen is a program over the database and the clock now (owner §45 D): a claim about its " +
    "runs rests on the database's runs being one at a time (2.6); the clock's time is the World's, which the world " +
    "moves on between runs and at each of its steps (owner §47), so a run of a search reads the world's time and " +
    "needs no such assumption of it; and " + keyed

  /** Where each node stands apart from today, each for a reason the design gives. */
  val standings: Map[String, List[String]] = Map(
    // Today's definitions, claims saying what each Declaration is (2.7): proven of what stands in them; today's
    // two definitions of two words each, a claim per word.
    "Adding" -> List("claim", "proven", "proven", ""),
    "Companies" -> List("claim", "proven", "proven", ""),
    "Ownership" -> List("claim", "proven", "proven", ""),
    "Searches" -> List("claim", "proven", "proven", ""),
    "SearchesAsk" -> List("claim", "proven", "proven", ""),
    "Sharing" -> List("claim", "proven", "proven", ""),
    // Today's definition of what the CRM holds, over provided values: a rule of the database's state now, the
    // World's (owner §45 D), proven of the code that changes it (cover_, start_).
    "CrmRun" -> List("claim", "proven", "proven", ""),
    // Gone: storing the rows about a record is the database model's operation, its meaning the model's.
    "StoreEdits" -> Nil,
    // The database's search, an operation known only by what is assumed of it (G2): its Scala tested against it on
    // the database's generated runs, reported beside tablesModel; and what it leaves, assumed as well.
    "SearchKeeps" -> List("assumption", "assumed", "proven", ""),
    // Split into parts: today's recordsByQuery, two assumptions; today's searchesMatch, implied by visibility.
    "RecordsByQuery" -> Nil,
    "SearchesMatch" -> Nil,
    "FetchesOnlyMatches" -> List("assumption", "assumed", "proven", ""),
    "FetchesEveryMatch" -> List("assumption", "assumed", "proven", ""),
    // A contract or an invariant is a claim (owner §15).
    "DealSearch" -> List("claim", "proven", "proven", ""),
    "ReadContract" -> List("claim", "proven", "proven", ""),
    "SharesExpire" -> List("claim", "proven", "proven", ""),
    "WriteContract" -> List("claim", "proven", "proven", ""),
    // The tables' one row per key (owner §40): trusted of the stores from outside, proven of every store the code
    // makes (made_, cover_); the database's facts its claim rests on (2.6, owner §36).
    "KeyedTables" -> List("assumption", "assumed", "proven", ""),
    "OneRowPerKey" -> List("claim", "proven", "proven", ""),
    "RunsOneAtATime" -> List("assumption", "assumed", "", ""),
    "TablesStartEmpty" -> List("assumption", "assumed", "", ""),
    // The model's Scala tested against it and against what is assumed of its search, today's 1,000 runs per
    // implementation: SQLite and the in-memory variant; that nothing else changes the database is an outside fact,
    // no Lean of its own.
    "TablesModel" -> List("assumption", "assumed", "", "2000"),
    // Today's contracts and invariant, claims (owner §15); today's expectations, roots of their own (owner §22).
    // Parents that only restated their parts, gone; the purpose's may read, a word of its own.
    "SaveWrite" -> Nil,
    "ExpiryJob" -> Nil,
    "Readers" -> List("claim", "proven", "proven", ""),
    // Today's expiryJobWiring's other decisions, designs of their own.
    "ExpirySchedule" -> List("design", "nothing to prove", "", ""),
    "DatabaseLock" -> List("design", "nothing to prove", "", ""),
    "AddedIsFound" -> List("claim", "proven", "proven", ""),
    "WritesLeaveOthers" -> List("claim", "proven", "proven", ""),
    "NoCrossTenantRead" -> List("claim", "proven", "proven", "")) ++
    // The parts, each a claim proven of the code (the screens', the write's, the write side's, the job's) or from
    // what the CRM's history does (what it holds).
    newParts.filterNot(_.startsWith("fetches")).map(_.capitalize -> List("claim", "proven", "proven", ""))

  /** None (owner §45 D done): the history and what the CRM holds are the database's, the World's (by G2); the clock
    * is the clock model's, the World's time, which the world moves on between runs (`elapse`) and at each of the
    * clock's steps in a run (owner §47). Every rule of crm is about the database's state alone, so time passing keeps
    * each by construction (`elapse` writes the clock only, and asks `cover_elapse` of no crm rule); the statements
    * reading the clock (`sharing`, the screens' claims) hold at whatever time a world holds, and a search reads the
    * world's time, its run's first look at the clock.
    */
  val provided: Map[String, frflow.project.Ported.OnD] = Map.empty

  /** What is not proven: nothing (step 12 rulings: a provided value an assumption pins is solved by it; the idle
    * try of the roots together; a step takes what the makers below it make).
    */
  val stopped: Map[String, List[String]] = Map.empty
