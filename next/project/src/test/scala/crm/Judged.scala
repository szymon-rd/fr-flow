package crm

/** What crm's port judges (`PortSuite`): each difference from today's in where a node sits and what it assumes, each
  * node standing apart from today's, and what is not proven, stopped on (the work list's questions).
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
    "tablesStartEmpty" -> ("new" -> ("what the database starts with, which a claim of always[CrmStore] rests on " +
      "as the database's state holds a store (2.6)")),
    "runsOneAtATime" -> ("new" -> "runs on the database never interleave, an assumption of the model (owner §36)"),
    "sharedCrm" -> ("companies, ownership, searches, searchesAsk, adding, sharing are parts" -> words),
    "storeMirrorsRequests" -> ("crmRun is a part; assumes +keyedTables" ->
      ("what the CRM holds, trusted, is an assumption, a part of the claim resting on it (owner §21); today's was a " +
        "definition. And " + keyed)),
    "visibility" -> ("noCrossTenantRead no part; assumes +keyedTables" ->
      ("noCrossTenantRead is a root (owner §40); visibility follows from searchesMatch and the code. And " + keyed)),
    "expiryJob" -> ("assumes +runsOneAtATime +keyedTables" ->
      ("a claim about a program's runs rests on the model's runs being atomic (2.6); and " + keyed))) ++
    List("dealSearch", "readContract", "searchesMatch", "noCrossTenantRead", "writesTakeEffect", "writesOnlyAsAsked",
      "recordsKept", "writeContract", "saveWrite", "sharesExpire").map(_ -> ("assumes +keyedTables" -> keyed))

  private def words = "today's definitions of the purpose's words are claims saying what each Declaration is, " +
    "parts of the purpose they are stated in (2.7)"
  private def keyed = "its Lean takes what always holds of every store, the tables' one row per key, which values " +
    "from outside meet by keyedTables (2.6, owner §40)"

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
    // Today's definition of what the CRM holds: trusted, an assumption (owner §21).
    "CrmRun" -> List("assumption", "assumed", "proven", ""),
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
    // The model's Scala tested against it, its runs capped at 200 per implementation (ModelRuns.Runs): SQLite and
    // the in-memory variant; that nothing else changes the database is an outside fact, no Lean of its own.
    "TablesModel" -> List("assumption", "assumed", "", "400"),
    // Stopped on (the work list's fourth question): what the CRM holds, by induction over its history, rests on
    // the steps' claims at stores the guard does not reach; and what rests on it, its roots' root_impl with it.
    "StoreMirrorsRequests" -> List("claim", "open", "open", ""),
    "SharedCrm" -> List("claim", "waiting", "waiting", ""),
    "AddedIsFound" -> List("claim", "open", "open", ""),
    "WritesLeaveOthers" -> List("claim", "open", "open", ""),
    "ExpiryJob" -> List("claim", "open", "open", ""),
    // Stopped on (the second question): a root met by doing nothing, and root_impl with the others.
    "NoCrossTenantRead" -> List("claim", "open", "open", ""))

  /** What is not proven, stopped on (the work list's questions). */
  val stopped: Map[String, List[String]] = Map(
    // The first question: the group of what the CRM holds, the write side and the database's store holds for every
    // value provided, and no store meets it for every history.
    "crmRun" -> List("Consistency"), "saveWrite" -> List("Consistency"), "storeEdits" -> List("Consistency"),
    // The fourth: what the CRM holds rests on crmRun (above), and its steps' claims are not asked of the stores
    // between (the work list); the roots resting on it, and root_impl of the roots with it.
    "storeMirrorsRequests" -> List("Check", "Parts"), "sharedCrm" -> List("Check"),
    "addedIsFound" -> List("Check", "RootImpl"), "writesLeaveOthers" -> List("Check", "RootImpl"),
    "expiryJob" -> List("Check", "RootImpl"),
    // The second: a root met by doing nothing (read and deals returning nothing).
    "noCrossTenantRead" -> List("Check", "Idle", "RootImpl"))
