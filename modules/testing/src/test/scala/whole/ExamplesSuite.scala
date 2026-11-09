package whole

import frflow.core.analysis.resolution.{Callees, Constrained}
import frflow.core.graph.Walk
import frflow.core.name.NodeId
import frflow.core.spec.Statement
import frflow.core.ty.Ty
import frflow.core.vocab.{Symbol, SymbolType}
import frflow.dsl.kb.FrModel

/** Every node of the five examples, written in the three kinds before any port (ARCHITECTURE.md, section 9, step 2):
  * each FrModel elaborates, its nodes are today's, named as today's, but for the differences listed, and the
  * analyses find no problem in it, but for those listed.
  */
class ExamplesSuite extends munit.FunSuite:
  private def ids(kb: FrModel): Set[String] = Theories.theory(kb).nodes.map(_.node.id.value).toSet

  private def kinds(kb: FrModel): Map[String, Int] = Theories.theory(kb).nodes.groupMapReduce(_.node.statement
    match
      case Statement.Claim(_, _)   => "claim"
      case Statement.Assumption(_) => "assumption"
      case Statement.Design(_)     => "design")(_ => 1)(_ + _)

  /** Today's nodes, less those the three kinds have no place for, with those they need added. */
  private def renamed(today: Set[String], dropped: Set[String], added: Set[String]): Set[String] =
    assert(dropped.subsetOf(today), dropped -- today)
    today -- dropped ++ added

  test("each example elaborates, with no error") {
    assertEquals(Today.all.map((name, kb) => name -> Theories.errors(kb)), Today.all.map(_._1 -> Nil))
  }

  test("rooms: today's nodes, named as today's, but onlyBookingWrites: the programs changing a store are derived " +
    "(owner §31); and the table's model is no assumption, nothing but the code changing it is (owner §36)") {
    assertEquals(ids(rooms.rooms), renamed(Today.rooms, Set("onlyBookingWrites", "tableMatchesModel"),
      Set("nothingElseWrites")))
    assertEquals(kinds(rooms.rooms), Map("claim" -> 12, "assumption" -> 4))
  }

  test("auth: today's, but the definition of two open types, which the types now say; and the session table's one " +
    "token per user, which today's function type said") {
    assertEquals(ids(auth.knowledge), renamed(Today.auth, Set("identities"), Set("tokensIssuedOnce")))
  }

  test("keycloak: today's, but the definition of four open types; the definition of `enabled` and `rolesOf` is two " +
    "claims; the claim on `introspect` named apart from it (owner §40); the server's store a model of the World, its " +
    "operations' assumptions, its rules' premises, its loaded accounts kept, the requests handed to it (owner §45 D)") {
    assertEquals(ids(keycloak.knowledge), renamed(Today.keycloak, Set("identities", "introspect"),
      Set("accountRoles", "introspectAnswers", "storeLogs", "lookupKeeps", "drawnTokens", "storeOnlyCode",
        "storeOneAtATime", "storeStarts", "loadedKept", "answersWhatItStores", "handedOneAtATime")))
  }

  test("crm: today's, with the root's two general expectations claims of their own (its scenario an example, and the " +
    "read contract's, owner §40); two definitions of two words each are four claims; runs on the database one at a " +
    "time, an assumption; the tables' one row per key a claim, with what the stores from outside meet and what the " +
    "database starts with (owner §40, 2.6); what the CRM holds the World's (owner §45 D): storing the rows about a " +
    "record the model's, no assumption, the search known only by what is assumed of it; the clock the World's time " +
    "(owner §47), no assumption; each node bundling several facts split into parts, searchesMatch implied by " +
    "visibility") {
    assertEquals(ids(crm.knowledge), renamed(Today.crm, Set("storeEdits", "searchesMatch", "recordsByQuery",
      "saveWrite", "expiryJob"),
      Set("addedIsFound", "writesLeaveOthers", "ownership", "searchesAsk", "runsOneAtATime", "keyedTables",
        "tablesStartEmpty", "oneRowPerKey", "searchKeeps", "readers", "expirySchedule", "databaseLock") ++
        crmParts))
  }

  /** Crm's parts: each one fact of a node of today's that bundled several. */
  private val crmParts = Set("recordsMirrorAdds", "sharesMirrorGrants", "fetchesOnlyMatches", "fetchesEveryMatch",
    "readsOnlyMatching", "readsOnlyReadable", "readsAllReadable", "dealsOnlyMatching", "dealsOnlyDeals",
    "dealsOnlyReadable", "dealsAllReadable", "writeKeepsRecords", "writeKeepsOthers", "writeDoesAsked",
    "writeOnlyAsked", "saveStores", "saveLogs", "saveReturns", "expiryKeepsRecords", "expiryKeepsLiveShares",
    "expiryKeepsLiveTimes", "jobStoresExpired", "jobLogsRun", "jobReturnsExpired")

  test("crm: the purpose and its two general expectations are roots (owner §22), each expectation proven from what " +
    "a search returns and what the CRM holds") {
    val refinement = Theories.theory(crm.knowledge).refinement
    val ids = Theories.theory(crm.knowledge).nodes.map(_.node.id)
    val roots = Set("sharedCrm", "addedIsFound", "writesLeaveOthers").map(NodeId(_))
    assertEquals(ids.filter(id => roots(id) && ids.exists(n => refinement.parts(n).contains(id))), Nil)
    assertEquals(List("addedIsFound", "writesLeaveOthers").map(id => refinement.parts(NodeId(id)).toSet),
      List.fill(2)(Set(NodeId("visibility"), NodeId("storeMirrorsRequests"))))
  }

  test("each example's examples elaborate, with no error") {
    val written = List(rooms.GrantedExamples(), auth.DecisionExamples(), keycloak.RequestExamples(),
      crm.WriteExamples(), crm.ExpireExamples())
    assertEquals(written.map(_.elaborated.fold(_.iterator.toList, _ => Nil)), List.fill(written.size)(Nil))
    assertEquals(written.map(_.examples.size), List(2, 5, 11, 6, 4))
  }

  test("sharing: today's, with the store's and the mail server's runs one at a time, assumptions; the definitions " +
    "of two words each are a claim per word, today's id kept for the first; the pool of connections a run of " +
    "delivery takes from and gives back (its bracket), its model's assumptions and its claim; the purpose's may edit " +
    "and is in the trash, Declarations, each with the claim saying what it is; the run the World's (owner §45 D, " +
    "§47): time never going back a claim of the clock, today's schedule a schedule of it, when housekeeping last ran " +
    "a model with its assumptions, what the branches hold at every moment rules of the World, each model's start") {
    assertEquals(ids(sharing.knowledge), renamed(Today.sharing, Set("clockNeverGoesBack", "clockKept"), Set(
      "oneTransactionAtATime", "mailOneAtATime", "editPermission", "reminderTime", "deliveryGivesBack",
      "poolKept", "poolOneAtATime", "whoMayEdit", "whatIsTrashed", "timeMovesOn", "housekeptLately",
      "nothingEndedAtHousekeeping", "logKept", "clockStarts", "housekeptStarts", "housekeptKept",
      "housekeptOneAtATime", "libraryStarts")))
    assertEquals(kinds(sharing.knowledge), Map("claim" -> 59, "assumption" -> 12, "design" -> 3))
  }

  test("the five examples are valid as written") {
    assertEquals(List(rooms.rooms, auth.knowledge, keycloak.knowledge, crm.knowledge, sharing.knowledge)
      .map(Theories.problems), List.fill(5)(Nil))
  }

  test("no example's proofs go round: what each node is proven from, followed down, never reaches it (crm and " +
    "sharing had circles through what their leaves relied on)") {
    Today.all.foreach { (name, kb) =>
      val r = Theories.resolved(kb)
      val ids = r.theory.nodes.map(_.node.id)
      assertEquals(ids.filter(id => Walk.breadthFirst(r.provenFrom(id), identity)(r.provenFrom).contains(id)), Nil,
        name)
    }
  }

  /** Each program Definition's error once resolved: what its code may fail with (`Failing`), read off its steps. */
  /** Each program's error, by its Definition (the operations on a state aside). */
  private def errors(kb: FrModel): Map[String, Option[Ty]] =
    val v = Theories.resolved(kb).theory.vocabulary
    v.symbols.collect {
      case Symbol(n, _, SymbolType.Typed(ty), _) if Ty.resultOf(ty).isInstanceOf[Ty.FlowOf] && v.modelOf(n).isEmpty =>
        n.value -> Ty.errorOf(ty)
    }.toMap

  test("each program's type says what it may fail with: sharing's, over the store and the mail server that may be " +
    "down, their failure; rooms' and crm's (the screens, the write side, the expiry job) nothing") {
    val failure = frflow.dsl.term.LeanType[sharing.domain.Failure].ty
    assertEquals(errors(sharing.knowledge), Map("handle" -> Some(failure), "housekeep" -> Some(failure),
      "deliver" -> Some(failure)))
    assertEquals((errors(rooms.rooms), errors(crm.knowledge)), (Map("book" -> None),
      Map("read" -> None, "deals" -> None, "save" -> None, "runExpiry" -> None)))
  }

  /** The parts of a node proven of code (`impl`) that are not about what the code calls: about its own Definitions
    * or Declarations. `impl` takes every part as a hypothesis, the code put in it (sound: each part is checked against
    * the same code, and the graph is acyclic), so these are valid as written.
    */
  private def notAboutCallees(kb: FrModel): List[(String, String)] =
    val t = Theories.theory(kb)
    for
      n    <- t.nodes.map(_.node.id)
      c    <- Callees.of(t, n).toList
      part <- t.refinement.parts(n)
      if !Constrained.of(t, part).exists(op => c.calls.symbols.contains(op) && !c.standsFor.contains(op))
    yield n.value -> part.value

  test("crm: the roots and the read side's claims, each about the screens' runs, rest on parts about those runs, " +
    "not read as calls of what the code calls; each node split into parts rests on its parts, about its own code") {
    assertEquals(notAboutCallees(crm.knowledge), List("addedIsFound" -> "storeMirrorsRequests",
      "addedIsFound" -> "visibility", "writesLeaveOthers" -> "storeMirrorsRequests",
      "writesLeaveOthers" -> "visibility",
      "visibility" -> "readContract", "visibility" -> "dealSearch", "noCrossTenantRead" -> "readsOnlyReadable",
      "noCrossTenantRead" -> "dealsOnlyReadable", "readContract" -> "readsOnlyMatching",
      "readContract" -> "readsOnlyReadable", "readContract" -> "readsAllReadable", "dealSearch" -> "dealsOnlyMatching",
      "dealSearch" -> "dealsOnlyDeals", "dealSearch" -> "dealsOnlyReadable", "dealSearch" -> "dealsAllReadable",
      "writeContract" -> "writeKeepsRecords", "writeContract" -> "writeKeepsOthers",
      "writeContract" -> "writeDoesAsked", "writeContract" -> "writeOnlyAsked", "sharesExpire" -> "expiryKeepsRecords",
      "sharesExpire" -> "expiryKeepsLiveShares", "sharesExpire" -> "expiryKeepsLiveTimes"))
  }

  test("sharing: its branches rest on the claims on their own operations' code, not on what that code calls") {
    val parts = notAboutCallees(sharing.knowledge)
    assertEquals(parts.map(_._1).distinct.toSet, Set("accessFollowsShares", "invitationsAreOffers",
      "trashUntilGone", "housekeepingClearsOnlyTheEnded", "accessRequestsAreAsks", "ownersKeepTheirDocuments",
      "auditTrail", "endedStaysEnded"))
    assertEquals(parts.size, 26)
  }
