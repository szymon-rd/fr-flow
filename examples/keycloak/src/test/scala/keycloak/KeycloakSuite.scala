package keycloak

import frflow.*
import cats.effect.IO
import frflow.api.{FrFlowError, LiveApi}
import frflow.check.Workspace
import java.nio.file.{Files, Paths}

class KeycloakSuite extends munit.CatsEffectSuite:
  // The API over the example's own workspace; nothing here decides, so no key is read.
  private def api =
    LiveApi(knowledge, Workspace(Paths.get("examples/keycloak").toAbsolutePath.normalize, "../../../lean"), sys.env.updated("FRFLOW_KEY", "no.key"))
  private def checked = api.flatMap(_.check(None)).recoverWith { case FrFlowError.LeanMissing => IO(assume(false, "lake is not available")) *> IO.never }

  test("the committed ledger accepts every node: none is up for review, none is gone") {
    // As `keycloak/run status` reads it: a change to the content, the hashes or the code fingerprints shows here.
    api.flatMap(_.view).map { v =>
      val annotated = v.annotated
      val states = annotated.nodes.map(r => r.id.value -> r.state.toString)
      assertEquals(states.size, knowledge.nodes.size)
      assertEquals(states.filter(_._2 != "accepted"), Nil)
      assertEquals(annotated.gone, Nil)
    }
  }

  test("the model is well formed: one root, refined by a DAG of parts; Introspect serves five parents") {
    assertEquals(knowledge.problems, Nil)
    assertEquals(knowledge.root.map(_.id), Some("RealmAccess"))
    assertEquals(knowledge.parentsOf(Introspection.introspect).map(_.id),
      List("AnswersNameASession", "DisabledHaveNoAccess", "RolesAsGranted", "SignedInAreAccepted", "RealmIsolation"))
    assertEquals(knowledge.parts(realmAccess).map(_.id), List("NoUnauthorizedAccess", "SignedInAreAccepted"))
  }

  test("the plain code is tested against its contracts: introspection, and the store's index and writes against their defines") {
    for c <- List(Introspection.introspect, sessionLookup, storeKeepsState) do
      val r = knowledge.test(c).getOrElse(fail(s"${c.id} is not tested"))
      assertEquals(r.failure, None, c.id)
      assertEquals(r.coverage.filter(_.held == 0), Nil, c.id)
  }

  test("an introspection that forgets the account's state fails a generated case") {
    val careless = knowledge.implement(Introspection.introspect, lookup)((realm, token) =>
      lookup.value(realm, token).map(x => Claims(realm, x.user, account.value(realm, x.user).fold(Nil)(_.roles))))
    val f = careless.test(Introspection.introspect).get.failure.getOrElse(fail("not found"))
    assert(f.why.contains("which Introspect refuses"), f)
  }

  test("every example passes, against its node and its code") {
    for n <- List(handleRequest, Introspection.introspect, sessionLookup, storeKeepsState) do
      val bad = knowledge.exampleResults(n).filter(r => r.contract != "ok" || r.implementation.exists(_ != "ok"))
      assert(bad.isEmpty, s"${n.id}: ${bad.map(r => r.example.describe + ": " + r.verdict).mkString("\n")}")
  }

  test("the running server: sign in, introspect in each realm, disable, sign out") {
    val realms = Realms(atStart, SessionDb.loaded(atStart))
    val opened = realms.handle(AuthRequest.SignIn(acme, "alice", "h-alice", "t1"))
    assert(opened.sessions.contains(Session("t1", acme, "alice")))
    assertEquals(realms.introspect(acme, "t1"), Some(Claims(acme, "alice", List("admin", "user"))))
    assertEquals(realms.introspect(globex, "t1"), None)
    assertEquals(realms.handle(AuthRequest.SignIn(acme, "bob", "h-bob", "t1")).sessions.count(_.token == "t1"), 1)
    assert(realms.setEnabled(acme, "alice", false))
    assertEquals(realms.introspect(acme, "t1"), None)
    assert(realms.setEnabled(acme, "alice", true))
    realms.handle(AuthRequest.SignOut(acme, "t1"))
    assertEquals(realms.introspect(acme, "t1"), None)
    assertEquals(realms.db.events().size, 5)
  }

  test("a store that drops a write is seen on the call: StoreKeepsState reads it back") {
    val dropping = knowledge.implementProven(storeKeepsState)(storedAs, (q, t) => ServerState(t.accounts, Nil))
    val handleSide = dropping.service(handleRequest)(sessionDb.bind(SessionDb.loaded(atStart)))
    val e = intercept[ContractViolation](handleSide(ServerState(atStart, Nil), AuthRequest.SignIn(acme, "alice", "h-alice", "t1")))
    assert(e.getMessage.contains("StoreKeepsState"), e.getMessage)
  }

  test("an index that answers with another realm's session is seen on the call: SessionLookup checks each answer") {
    val leaky = knowledge.implementProven(sessionLookup)(storedSession, (realm, token) => Some(Session(token, globex, "carol")))
    val db = SessionDb.loaded(atStart)
    val introspectSide = leaky.service(Introspection.introspect)(sessionDb.bind(db), seed.bind(atStart), history.bind(db.events()),
      sessions.bind((r: RealmId) => db.load().sessions.filter(_.realm == r)),
      account.bind((r: RealmId, u: String) => accountOf.fn(db.load().accounts, r, u)))
    val e = intercept[ContractViolation](introspectSide(acme, "t9"))
    assert(e.getMessage.contains("SessionLookup"), e.getMessage)
  }
