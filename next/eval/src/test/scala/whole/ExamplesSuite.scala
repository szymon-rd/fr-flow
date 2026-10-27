package whole

import frflow.core.analysis.{Callees, Constrained}
import frflow.core.graph.Walk
import frflow.core.ty.Ty
import frflow.core.vocab.{Symbol, SymbolType}
import frflow.core.spec.Statement
import frflow.dsl.kb.KnowledgeBase

/** Every node of the five examples, written in the three kinds before any port (ARCHITECTURE.md, section 9, step 2):
  * each knowledge base elaborates, its nodes are today's, named as today's, but for the differences listed, and the
  * analyses find no problem in it, but for those listed.
  */
class ExamplesSuite extends munit.FunSuite:
  private def ids(kb: KnowledgeBase): Set[String] = Theories.theory(kb).nodes.map(_.node.id.value).toSet

  private def kinds(kb: KnowledgeBase): Map[String, Int] = Theories.theory(kb).nodes.groupMapReduce(_.node.statement
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

  test("rooms: today's nodes, named as today's") {
    assertEquals(ids(rooms.rooms), Today.rooms)
    assertEquals(kinds(rooms.rooms), Map("claim" -> 8, "assumption" -> 5))
  }

  test("auth: today's, but the definition of two open types, which the types now say; and the session table's one " +
    "token per user, which today's function type said") {
    assertEquals(ids(auth.knowledge), renamed(Today.auth, Set("identities"), Set("tokensIssuedOnce")))
  }

  test("keycloak: today's, but the definition of four open types; the definition of `enabled` and `rolesOf` is two " +
    "claims") {
    assertEquals(ids(keycloak.knowledge), renamed(Today.keycloak, Set("identities"), Set("accountRoles")))
  }

  test("crm: today's, with the root's two general expectations and the read contract's one claims of their own " +
    "(its scenario an example); two definitions of two words each are four claims; runs on the database one at a " +
    "time, an assumption") {
    assertEquals(ids(crm.knowledge), renamed(Today.crm, Set.empty, Set("addedIsFound", "writesLeaveOthers",
      "acmeNeverSeesGlobex", "ownership", "searchesAsk", "runsOneAtATime")))
  }

  test("each example's examples elaborate, with no error") {
    val written = List(rooms.GrantedExamples(), auth.DecisionExamples(), crm.ExpectationsExamples())
    assertEquals(written.map(_.elaborated.fold(_.iterator.toList, _ => Nil)), List.fill(written.size)(Nil))
    assertEquals(written.map(_.examples.size), List(2, 5, 1))
  }

  test("sharing: today's, with the store's, the mail server's and the clock's runs one at a time, assumptions; the " +
    "definitions of two words each are a claim per word, today's id kept for the first") {
    assertEquals(ids(sharing.knowledge), renamed(Today.sharing, Set.empty, Set(
      "oneTransactionAtATime", "mailOneAtATime", "clockAlone", "editPermission", "reminderTime")))
    assertEquals(kinds(sharing.knowledge), Map("claim" -> 52, "assumption" -> 8, "design" -> 3))
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
  private def errors(kb: KnowledgeBase): Map[String, Option[Ty]] =
    Theories.resolved(kb).theory.vocabulary.symbols.collect {
      case Symbol(n, _, SymbolType.Typed(ty), _) if Ty.resultOf(ty).isInstanceOf[Ty.FlowOf] => n.value -> Ty.errorOf(ty)
    }.toMap

  test("each program's type says what it may fail with: sharing's, over the store and the mail server that may be " +
    "down, their failure; rooms' and crm's nothing") {
    val failure = frflow.dsl.term.LeanType[sharing.domain.Failure].ty
    assertEquals(errors(sharing.knowledge), Map("handle" -> Some(failure), "housekeep" -> Some(failure),
      "deliver" -> Some(failure)))
    assertEquals((errors(rooms.rooms), errors(crm.knowledge)), (Map("book" -> None), Map("runExpiry" -> None)))
  }

  /** The parts of a node proven of code (`impl`) that are not about what the code calls: about its own Definitions
    * or Declarations. `impl` takes every part as a hypothesis, the code put in it (sound: each part is checked against
    * the same code, and the graph is acyclic), so these are valid as written.
    */
  private def notAboutCallees(kb: KnowledgeBase): List[(String, String)] =
    val t = Theories.theory(kb)
    for
      n    <- t.nodes.map(_.node.id)
      c    <- Callees.of(t, n).toList
      part <- t.refinement.parts(n)
      if !Constrained.of(t, part).exists(op => c.calls.symbols.contains(op) && !c.standsFor.contains(op))
    yield n.value -> part.value

  test("crm: the root's expectations and the records kept by the expiry job rest on parts not about what their " +
    "code calls") {
    assertEquals(notAboutCallees(crm.knowledge), List("addedIsFound" -> "sharedCrm", "writesLeaveOthers" -> "sharedCrm",
      "recordsKept" -> "sharesExpire"))
  }

  test("sharing: its branches rest on the claims on their own operations' code, not on what that code calls") {
    val parts = notAboutCallees(sharing.knowledge)
    assertEquals(parts.map(_._1).distinct.toSet, Set("accessFollowsShares", "invitationsAreOffers",
      "trashUntilGone", "housekeepingClearsOnlyTheEnded", "accessRequestsAreAsks", "ownersKeepTheirDocuments",
      "auditTrail", "noticesFollowChanges", "trashPurgedOnTime", "invitationsLapseOnTime", "requestsAnsweredOnTime",
      "endedStaysEnded"))
    assertEquals(parts.size, 34)
  }
