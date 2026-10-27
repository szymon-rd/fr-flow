package frflow.reference

import _root_.keycloak.*

/** keycloak's seeded bugs, as `KeycloakSuite` seeds them. */
object KeycloakBugs:
  def all: List[Seeded] = List(dropping, leaky, careless)

  private def dropping: Seeded =
    val kb = knowledge.implementProven(storeKeepsState)(storedAs, (q, t) => ServerState(t.accounts, Nil))
    val handle = kb.service(handleRequest)(sessionDb.bind(SessionDb.loaded(atStart)))
    Seeded("dropping store", inTable = true,
      "storeKeepsState's code beside storedAs keeps the accounts and drops every session: " +
        "(q, t) => ServerState(t.accounts, Nil)",
      "KeycloakSuite: a store that drops a write is seen on the call: StoreKeepsState reads it back",
      Stops.onCall("""handleRequest(ServerState(atStart, Nil), SignIn(acme, "alice", "h-alice", "t1"))""")(
        handle(ServerState(atStart, Nil), AuthRequest.SignIn(acme, "alice", "h-alice", "t1"))) ++
        Stops.generated(kb, storeKeepsState) ++ Stops.examples(kb, storeKeepsState))

  private def leaky: Seeded =
    val kb = knowledge.implementProven(sessionLookup)(storedSession,
      (realm, token) => Some(Session(token, globex, "carol")))
    val db = SessionDb.loaded(atStart)
    val introspectSide = kb.service(Introspection.introspect)(sessionDb.bind(db), seed.bind(atStart),
      history.bind(db.events()), sessions.bind((r: RealmId) => db.load().sessions.filter(_.realm == r)),
      account.bind((r: RealmId, u: String) => accountOf.fn(db.load().accounts, r, u)))
    Seeded("leaky introspection", inTable = true,
      "sessionLookup's code beside storedSession answers every lookup with another realm's session (globex, carol)",
      "KeycloakSuite: an index that answers with another realm's session is seen on the call: SessionLookup checks " +
        "each answer",
      Stops.onCall("""introspect(acme, "t9") on the loaded sessions""")(introspectSide(acme, "t9")) ++
        Stops.generated(kb, sessionLookup) ++ Stops.examples(kb, sessionLookup))

  private def careless: Seeded =
    val kb = knowledge.implementTested(Introspection.introspect, lookup)((realm, token) =>
      lookup.value(realm, token).map(x => Claims(realm, x.user, account.value(realm, x.user).fold(Nil)(_.roles))))
    Seeded("introspection that forgets the account's state", inTable = false,
      "Introspect implemented without the check that the account is still enabled",
      "KeycloakSuite: an introspection that forgets the account's state fails a generated case",
      Stops.generated(kb, Introspection.introspect) ++ Stops.examples(kb, Introspection.introspect))
