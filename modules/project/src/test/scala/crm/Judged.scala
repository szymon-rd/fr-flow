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
    "sharedCrm" -> ("companies, ownership, searches, searchesAsk, adding, sharing are parts; assumes +keyedTables" ->
      (words + "; and " + keyed + ", the words read in the World (searches reads the screens' runs)")),
    "storeMirrorsRequests" -> ("assumes +keyedTables" -> keyed),
    "visibility" -> ("noCrossTenantRead no part; assumes +keyedTables +runsOneAtATime" ->
      ("noCrossTenantRead is a root (owner §40); visibility follows from searchesMatch and the code. And " + runs)),
    "saveWrite" -> ("assumes +runsOneAtATime +keyedTables" -> ("the write side is a program over the database now " +
      "(owner §45 D): its claim says what a run leaves and gives, which rests on the database's runs being atomic " +
      "(2.6); and " + keyed)),
    "expiryJob" -> ("assumes +runsOneAtATime +keyedTables" ->
      ("a claim about a program's runs rests on the model's runs being atomic (2.6); and " + keyed))) ++
    List("writesTakeEffect", "writesOnlyAsAsked", "recordsKept").map(_ -> ("saveWrite no part; assumes +keyedTables" ->
      ("what the database holds after the write side saves a write is what the write's code leads to (afterSave " +
        "over applyWrite: a rule reads values, not a Definition left open), proven of the write's code: the write " +
        "side's run, saveWrite, no part of it; and " + keyed))) ++
    List("dealSearch", "readContract", "noCrossTenantRead", "searchesMatch").map(_ ->
      ("assumes +keyedTables +runsOneAtATime" -> runs)) ++
    List("writeContract", "sharesExpire").map(_ -> ("assumes +keyedTables" -> keyed))

  private def words = "today's definitions of the purpose's words are claims saying what each Declaration is, " +
    "parts of the purpose they are stated in (2.7)"
  private def keyed = "its Lean takes what always holds of every store, the tables' one row per key, which values " +
    "from outside meet by keyedTables (2.6, owner §40)"
  private def runs = "a screen is a program over the database and the clock now (owner §45 D): a claim about its " +
    "runs rests on the database's runs being atomic (2.6); the clock's time is the World's, which the world moves on " +
    "between runs and at each of its steps (owner §47), so a run of a search reads the world's time and needs no " +
    "atomic of it; and " + keyed

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
    "RecordsByQuery" -> List("assumption", "assumed", "proven", ""),
    "SearchKeeps" -> List("assumption", "assumed", "proven", ""),
    // A contract or an invariant is a claim (owner §15).
    "DealSearch" -> List("claim", "proven", "proven", ""),
    "ReadContract" -> List("claim", "proven", "proven", ""),
    "SaveWrite" -> List("claim", "proven", "proven", ""),
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
    "ExpiryJob" -> List("claim", "proven", "proven", ""),
    "AddedIsFound" -> List("claim", "proven", "proven", ""),
    "WritesLeaveOthers" -> List("claim", "proven", "proven", ""),
    "NoCrossTenantRead" -> List("claim", "proven", "proven", ""))

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
