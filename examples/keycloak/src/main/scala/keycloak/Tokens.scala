package keycloak

import frflow.*

// ============================================================================
// Root: what an application learns from a token, generic
// ============================================================================

val Realm = Opaque("Realm", "an organisation using the server, with its own users and applications")
val User  = Opaque("User", "a person with an account in a realm")
val Token = Opaque("Token", "what a user hands an application after signing in")

val openIn    = Param[(Token.T, Realm.T) => Boolean]("openIn", "whether the token names a session open in the realm")
val holder    = Param[Token.T => Option[User.T]]("holder", "the user whose session the token names, if it names one")
val enabledIn = Param[(Realm.T, User.T) => Boolean]("enabledIn", "whether the user is an enabled user of the realm")

/** Model: what the server tells a realm's application about a token: whose it is, if anyone's. */
val tokenCheck = Node.root[(Realm.T, Token.T) => Option[User.T]](
  "TokenCheck",
  "A realm's application learns whose a token is exactly when the token's session is open in that realm and its user is enabled there.",
  why = "The idea's second section: applications ask whose a token is, and must get the answer when the session is open and the user enabled, and never otherwise. 'Open in that realm' also says a token is only good in the realm that issued it. Sessions, users and realms are left open.",
  idea = "Checking tokens"
)(whose => forall((r: Realm.T, t: Token.T) =>
  whose(r, t).forall(u => openIn(t, r) && holder(t) == Some(u) && enabledIn(r, u)) &&
  (openIn(t, r) ==> holder(t).forall(u => enabledIn(r, u) ==> (whose(r, t) == Some(u))))))

// ============================================================================
// Instantiation: tokens are references to stored sessions
// ============================================================================

val sessionsByToken = Param[String => Option[Session]]("sessionsByToken",
  "the open session each token names, as stored when the request is decided (SignInOut keeps tokens distinct)")

/** The user of a token's session, if it names one. */
val sessionUser = define { (t: String) =>
  sessionsByToken(t) match
    case Some(s) => Some(s.user)
    case None    => None
}

/** Whether a user of the realm, enabled, has this username. */
val isEnabled = define { (r: RealmId, u: String) => users.value.exists(a => a.realm == r && a.username == u && a.enabled) }

val referenceTokens = tokenCheck.instantiate[(RealmId, String) => Option[String]](
  "ReferenceTokens",
  "Tokens are random strings that name a stored session; a token is open in a realm when its stored session is of that realm; a user is enabled as their account says.",
  why = "A token carries nothing but a reference, so every check reads the session store: a sign-out or a disabled account takes effect at the next check. The cost is a lookup per check, which one server answers from memory."
)(
  Realm     := of[RealmId],
  User      := of[String],
  Token     := of[String],
  openIn    := ((t: String, r: RealmId) => sessionsByToken(t).exists(s => s.realm == r)),
  holder    := ((t: String) => sessionUser(t)),
  enabledIn := ((r: RealmId, u: String) => isEnabled(r, u))
).relies(sessionTable, "a token names at most one session: sign-ins keep tokens distinct, and a sign-out removes the session from the store")

// ============================================================================
// Port: the session store, outside the proven core
// ============================================================================

val sessionDb = Param[SessionDb]("sessionDb", "the in-memory session store the server keeps, indexed by realm and token")

/** What the store is trusted to do: return the session a token names in a realm, and nothing of another realm. */
val sessionLookup = Node.port[RealmId, String, Option[Session]](
  "SessionLookup",
  "The session store returns the realm's open session a token names, if there is one, and never a session of another realm.",
  why = "Sessions live in a store indexed by realm and token (in memory here; a database or cache in a cluster). Introspection is proven from this promise, not from the index; the index is checked against the define it is decided with on its examples, and every session it returns is checked to be of the realm asked."
)((realm, token, r) => r.forall(s => sessionsByToken(token) == Some(s) && s.realm == realm) &&
  sessionsByToken(token).forall(s => (s.realm == realm) ==> (r == Some(s))))
  .checkedBy((realm, token, r) => r.forall(s => s.realm == realm))
  .examples(sessionsByToken.bindTable(Map("t1" -> Session("t1", RealmId("acme"), "alice"))), sessionDb.bind(SessionDb.of(List(Session("t1", RealmId("acme"), "alice")))))(
    expect(RealmId("acme"), "t1", Some(Session("t1", RealmId("acme"), "alice")), "acme's session of t1"),
    expect(RealmId("globex"), "t1", None, "the store keeps sessions per realm: none of globex under t1"),
    reject(RealmId("acme"), "t1", None, "an open session is never lost"),
    reject(RealmId("globex"), "t1", Some(Session("t1", RealmId("acme"), "alice")), "another realm's session is never returned"))

/** The session a token names in a realm, as the port promises it: what the index is checked against. */
val storedSession = define { (realm: RealmId, token: String) =>
  sessionsByToken(token) match
    case Some(s) => if s.realm == realm then Some(s) else None
    case None    => None
}

// ============================================================================
// Contract: one introspection request
// ============================================================================

/** The user named by an answer, if any. */
val claimedUser = define { (c: Option[Claims]) =>
  c match
    case Some(x) => Some(x.user)
    case None    => None
}

val introspectContract = referenceTokens.contractVia[RealmId, String, Option[Claims]](
  "Introspect",
  "An introspection answers with the token's user and their roles exactly when the token's session is open in the realm asking and the user is enabled there; the claims name that realm.",
  why = "ReferenceTokens for one request, as Keycloak's introspection endpoint answers it: the claims carry the user's realm roles, which applications use to authorise. abs: the user an answer names."
)(abs = f => (r, t) => claimedUser(f(r, t)))((realm, token, res) =>
  res.forall(c => c.realm == realm && sessionsByToken(token).exists(s => s.realm == realm && s.user == c.user) &&
    users.value.exists(a => a.realm == realm && a.username == c.user && a.enabled && a.roles == c.roles)) &&
  sessionsByToken(token).forall(s => (s.realm == realm && isEnabled(realm, s.user)) ==> res.isDefined))
  .examples(
    users.bind(List(UserAccount(RealmId("acme"), "alice", "h-alice", true, List("admin", "user")), UserAccount(RealmId("acme"), "bob", "h-bob", false, List("user")))),
    sessionsByToken.bindTable(Map("t1" -> Session("t1", RealmId("acme"), "alice"), "t2" -> Session("t2", RealmId("acme"), "bob"))),
    sessionDb.bind(SessionDb.of(List(Session("t1", RealmId("acme"), "alice"), Session("t2", RealmId("acme"), "bob")))))(
    expect(RealmId("acme"), "t1", Some(Claims(RealmId("acme"), "alice", List("admin", "user"))), "Alice's token at acme: active, with her roles"),
    expect(RealmId("globex"), "t1", None, "acme's token is not good at globex"),
    expect(RealmId("acme"), "t2", None, "Bob was disabled after signing in: his token is no longer active"),
    expect(RealmId("acme"), "t9", None, "no session: signed out, or never issued"),
    reject(RealmId("globex"), "t1", Some(Claims(RealmId("globex"), "alice", List("admin", "user"))), "a token is never good in another realm"),
    reject(RealmId("acme"), "t2", Some(Claims(RealmId("acme"), "bob", List("user"))), "a disabled user's token is never active"),
    reject(RealmId("acme"), "t1", Some(Claims(RealmId("acme"), "alice", List("admin", "user", "owner"))), "roles are never made up"),
    reject(RealmId("acme"), "t1", None, "an active token is not turned away"))
  .keeps(realmIsolation)((realm, token, res) => res match
    case Some(c) => List((realm, c))
    case None    => Nil)
  .expects("A token with no stored session is never active, in any realm")(f =>
    forall((r: RealmId, t: String) => (sessionsByToken(t) == None) ==> (f(r, t) == None)))

/** In introspection's code: the session store, called by its promise. */
val lookup = sessionLookup.caller("lookup")

/** An introspection: the realm's session the token names, its user's account if enabled, and their roles. */
val introspect = define { (realm: RealmId, token: String) =>
  lookup(realm, token) match
    case Some(s) =>
      users.value.find(a => a.realm == realm && a.username == s.user && a.enabled) match
        case Some(a) => Some(Claims(realm, a.username, a.roles))
        case None    => None
    case None => None
}
