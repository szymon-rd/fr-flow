package whole

import frflow.core.analysis.Problem
import frflow.core.name.NodeId
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
    "definitions of two words each are a claim per word") {
    assertEquals(ids(sharing.knowledge), renamed(Today.sharing, Set("permission", "requestLifetime"), Set(
      "oneTransactionAtATime", "mailOneAtATime", "clockAlone", "mayView", "mayEdit", "requestLasts", "remindAfter")))
    assertEquals(kinds(sharing.knowledge), Map("claim" -> 52, "assumption" -> 8, "design" -> 3))
  }

  test("rooms, auth and keycloak are valid as written") {
    assertEquals(List(rooms.rooms, auth.knowledge, keycloak.knowledge).map(Theories.problems), List.fill(3)(Nil))
  }

  /** The parts the analyses refuse: a claim mentioning a Definition with proven code is proven of that code
    * (`impl`), from parts about what the code calls, never from parts about the Definition itself (`PartNotCalled`).
    * Today's crm and sharing prove such claims from claims on the same operations (reported, with a proposal).
    */
  private def notCalled(kb: KnowledgeBase): List[(String, String)] =
    val problems = Theories.problems(kb)
    val parts = problems.collect { case Problem.PartNotCalled(id, part) => (id.value, part.value) }
    assertEquals(problems.filterNot(_.isInstanceOf[Problem.PartNotCalled]), Nil)
    assert(parts.forall((id, part) => Theories.theory(kb).refinement.parts(NodeId(id)).contains(NodeId(part))))
    parts

  test("crm is valid but for the claims proven from claims on their own code: the root's expectations, and the " +
    "records kept by the expiry job") {
    assertEquals(notCalled(crm.knowledge), List("addedIsFound" -> "sharedCrm", "writesLeaveOthers" -> "sharedCrm",
      "recordsKept" -> "sharesExpire"))
  }

  test("sharing is valid but for its branches proven from the claims on their own operations' code") {
    val parts = notCalled(sharing.knowledge)
    assertEquals(parts.map(_._1).distinct.toSet, Set("accessFollowsShares", "invitationsAreOffers",
      "trashUntilGone", "housekeepingClearsOnlyTheEnded", "accessRequestsAreAsks", "ownersKeepTheirDocuments",
      "auditTrail", "noticesFollowChanges", "trashPurgedOnTime", "invitationsLapseOnTime", "requestsAnsweredOnTime",
      "endedStaysEnded"))
    assertEquals(parts.size, 34)
  }
