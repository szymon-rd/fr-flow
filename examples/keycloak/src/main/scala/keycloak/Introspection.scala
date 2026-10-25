package keycloak

import frflow.*

// ============================================================================
// Checking tokens: applications ask the server whose a token is
// ============================================================================

/** What the server tells a realm's application about a token: the realm, the user, their realm roles. */
final case class Claims(realm: RealmId, user: String, roles: List[String])
object Claims extends Data[Claims]

val introspect = Param[(RealmId, String) => Option[Claims]]("introspect",
  "the server's answer to a realm's application asking about a token: the claims it is active with, or none (not active)")

/** The user and roles an answer names, if any. */
val claimsOf = define { (c: Term[Option[Claims]]) =>
  c.fold(none[(String, List[String])])(x => some((x.user, x.roles)))
}

val referenceTokens = Node.definition("ReferenceTokens",
  "A realm's application accepts a token as the server's introspection of it answers: a token is a reference to a session the server holds, not a statement the application reads.",
  why = "Sign-out must end a token at once, and a disabled user must lose access at once: a signed token stays good after both until it expires, so applications ask the server about every token. The cost is a lookup per check, which one server answers from memory."
)(accepted := ((r: Term[RealmId], t: Term[String]) => claimsOf(introspect(r, t))))

val realmIsolation = Node.invariant[RealmId, Claims]("RealmIsolation",
  "No application is ever shown claims of a realm other than its own.",
  why = "The idea says a token is only ever good in the realm that issued it. Stated once over every answer the server gives, so a new endpoint (user info, an admin view of sessions) must keep it or say why not.",
  idea = "Realms"
)((asking, c) => c.realm === asking)
  .under(onlyTheSignedIn)

val answersNameASession = Node.claim("AnswersNameASession",
  "An introspection answers only with the realm and user of a session the server holds under the token.",
  why = "A token is a reference to a session: what the server says about it must come from that session, not from the token or the request.",
  idea = "Checking tokens"
)(forall((r: Term[RealmId], t: Term[String]) => introspect(r, t).forall(c => sessions(c.realm).contains(Session(t, c.realm, c.user)))))
  .under(onlyTheSignedIn)

/** Whether `x` is the only session the list holds under its token. */
val onlyOne = define { (ss: Term[List[Session]], x: Term[Session]) => ss.forall(y => (y.token === x.token) ==> (y === x)) }

val introspectContract = Node.contract(introspect)("Introspect",
  "An introspection names the realm asking, and a user enabled there with their roles, only for a session that realm holds under the token; and it names that session's user whenever the user is enabled and the token names no other session there.",
  why = "Keycloak's introspection endpoint, for one request, so each answer of the running server is checked. The claims carry the user's realm roles, which applications use to authorise.",
  idea = "Checking tokens"
)((realm, token, res) =>
  res.forall(c => c.realm === realm && sessions(c.realm).contains(Session(token, c.realm, c.user)) &&
    isEnabled(account(realm, c.user)) && c.roles === rolesIn(account(realm, c.user))) &&
  sessions(realm).forall(x => (x.token === token && isEnabled(account(realm, x.user)) && onlyOne(sessions(realm), x)) ==>
    (res === some(Claims(realm, x.user, rolesIn(account(realm, x.user)))))))
  .under(answersNameASession, disabledHaveNoAccess, rolesAsGranted, signedInAreAccepted)
  .keeps(realmIsolation)((realm, token, res) => res
    .fold(List.empty[(RealmId, Claims)])(c => List((realm, c))))
  .examples(history.bind(events), seed.bind(atStart), sessionDb.bind(SessionDb.replaying(seed.value, history.value)))(
    expect(acme, "t1", Some(Claims(acme, "alice", List("admin", "user"))), "Alice's token at acme: accepted as hers, with her roles"),
    expect(globex, "t4", Some(Claims(globex, "carol", List("viewer"))), "Carol's token at globex: accepted as hers"),
    expect(globex, "t1", None, "acme's token is not good at globex"),
    expect(acme, "t2", None, "Bob was disabled after signing in: his token is no longer accepted"),
    expect(acme, "t3", None, "Alice signed out with t3"),
    expect(acme, "t9", None, "a token no sign-in got"),
    reject(globex, "t1", Some(Claims(globex, "alice", List("admin", "user"))), "a token is never good in another realm"),
    reject(acme, "t4", Some(Claims(acme, "carol", List("viewer"))), "nor is globex's token good at acme"),
    reject(acme, "t2", Some(Claims(acme, "bob", List("user"))), "a disabled user's token is never accepted"),
    reject(acme, "t3", Some(Claims(acme, "alice", List("admin", "user"))), "a token signed out with is never accepted again"),
    reject(acme, "t1", Some(Claims(acme, "alice", List("admin", "user", "owner"))), "roles are never made up"),
    reject(acme, "t1", None, "Alice's token is not turned away"))

// ============================================================================
// Looking up a session: the store, outside the proven core
// ============================================================================

val lookup = Param[(RealmId, String) => Option[Session]]("lookup",
  "the store's answer to looking up a token's session in a realm, from its index by realm and token")

val sessionLookup = Node.assumption(lookup)("SessionLookup",
  "The store's index returns a session it holds under the token in the realm asked, if it holds one, and never one of another realm or token.",
  why = "Sessions live in a store indexed by realm and token (in memory here; a database or cache in a cluster). Introspection is proven from this promise, not from the index; the index is checked against the define it is decided with on its examples, and every session it returns is checked to be of the realm and token asked."
)((realm, token, r) => r.forall(x => sessions(realm).contains(x) && x.token === token && x.realm === realm) &&
  (sessions(realm).exists(x => x.token === token) ==> r.isDefined))
  .checkedBy((realm, token, r) => r.forall(x => x.token === token && x.realm === realm))
  .examples(history.bind(events), seed.bind(atStart), sessionDb.bind(SessionDb.replaying(seed.value, history.value)))(
    expect(acme, "t1", Some(Session("t1", acme, "alice")), "acme's session of t1"),
    expect(globex, "t1", None, "the store keeps sessions per realm: none of globex under t1"),
    expect(acme, "t3", None, "Alice signed out with t3: its session is gone"),
    reject(acme, "t1", None, "a session the store holds is never lost"),
    reject(globex, "t1", Some(Session("t1", acme, "alice")), "another realm's session is never returned"))

/** The session the store holds under a token in a realm: what the index is checked against. */
val storedSession = define { (realm: Term[RealmId], token: Term[String]) => sessions(realm).find(x => x.token === token && x.realm === realm) }

/** An introspection, in plain Scala: the realm's session the token names, if its user is enabled there, with their
  * roles. Not proven: `check` tests it against Introspect, and the proofs above rest on that contract.
  */
def introspection(realm: RealmId, token: String): Option[Claims] =
  for
    x <- lookup.value(realm, token)
    a <- account.value(realm, x.user) if a.enabled
  yield Claims(realm, x.user, a.roles)
