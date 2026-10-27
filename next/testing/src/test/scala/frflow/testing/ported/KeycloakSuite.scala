package frflow.testing.ported

import frflow.*
import frflow.eval.run.Broken
import keycloak.*

/** Keycloak's generated tests (today's `KeycloakSuite`, its testing cases' names kept): the plain code against the
  * claims and assumptions on it, and section 9's two seeded bugs, each caught by a failing generated case.
  */
class KeycloakSuite extends munit.FunSuite:
  /** Keycloak with `introspect` and `record` given other code. */
  private type Introspecting =
    ((RealmId, String) => Option[Session], (RealmId, String) => Option[UserAccount]) => (RealmId, String) => Option[Claims]

  private def with_(introspected: Introspecting, recorded: (AuthRequest, ServerState) => ServerState): KnowledgeBase =
    KnowledgeBase("Keycloak")(knowledge.nodes*).implementProvided(seed, history, state)
      .implementProven(step)(handle)
      .implementTested(record)(_ => recorded)
      .implementTested(lookup)(env => (realm, token) => SessionDb.holding(env(state)).find(realm, token))
      .implementTested(introspect, lookup, account)(env => introspected(env(lookup), env(account)))

  test("the plain code is tested against its contracts: introspection, and the store's index and writes") {
    assertEquals(Tested.nodes(knowledge).sorted,
      List("answersNameASession", "introspect", "realmIsolation", "sessionLookup", "storeKeepsState"))
    Tested.nodes(knowledge).foreach(n =>
      assertEquals(Tested.report(knowledge, n).map(r => (r.failure, r.unreached)), Some((None, Nil)), n))
  }

  test("an introspection that forgets the account's state fails a generated case") {
    val leaky = with_((lookUp, accountOf) => (r, t) =>
      lookUp(r, t).flatMap(x => accountOf(r, x.user).map(a => Claims(r, x.user, a.roles))),
      (q, after) => SessionDb.holding(after).storeAfter(q, after))
    assertEquals(Tested.failure(leaky, "introspect").broke, Broken.Post)
  }

  test("a store that drops the sessions it is given fails a generated case of storeKeepsState") {
    val dropping = with_((lookUp, accountOf) => introspection(lookUp, accountOf),
      (_, after) => after.copy(sessions = Nil))
    assertEquals(Tested.failure(dropping, "storeKeepsState").broke, Broken.Post)
  }
