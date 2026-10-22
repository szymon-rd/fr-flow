package keycloak

import frflow.*

// ============================================================================
// Root: signing in and out, over every sequence of requests
// ============================================================================

val Store   = Opaque("Store", "the sessions the server keeps open")
val Request = Opaque("Request", "a sign-in or a sign-out sent to the server")

val initial  = Param[Store.T]("initial", "the store the server starts with")
val distinct = Param[Store.T => Boolean]("distinct", "whether no two open sessions share a token")
val granted  = Param[(Store.T, Request.T, Store.T) => Boolean]("granted",
  "whether the second store holds what the request asked for, when it may be granted: a session for a sign-in by an enabled user with their password, the end of the session for a sign-out")
val onlyThat = Param[(Store.T, Request.T, Store.T) => Boolean]("onlyThat",
  "whether the change from the first store to the second is only what the request may make: a session opens only for an enabled user with their password, and no other session changes")

/** Model: the store a sequence of requests leads to, from the initial store. */
val sessions = Node.root[List[Request.T] => Store.T](
  "Sessions",
  "In every store the server reaches, tokens are distinct; every sign-in or sign-out is granted when it may be, and changes nothing else.",
  why = "The idea's first section, over every sequence of requests: a user can sign in and out (granted), nobody else gets a session (onlyThat), and a token names one session (distinct). What a store, a request and each rule are is left open.",
  idea = "Signing in and out"
)(run => forall((rs: List[Request.T]) => distinct(run(rs))) &&
  forall((rs: List[Request.T], q: Request.T) => onlyThat(run(rs), q, run(rs ++ List(q))) && granted(run(rs), q, run(rs ++ List(q)))))

/** Model: one request. */
val oneAtATime = sessions.refine[(Store.T, Request.T) => Store.T](
  "OneAtATime",
  "The server starts with distinct tokens, a request keeps tokens distinct, and every request is granted when it may be and changes nothing else.",
  why = "The server handles requests one at a time from its initial store, so it is enough that the start has distinct tokens and each step keeps them distinct (by induction over the requests), and that each step does only what was asked. abs: the store after a sequence is the requests applied in turn."
)(
  abs  = apply => rs => rs.foldLeft(initial.value)((s, q) => apply(s, q)),
  spec = apply => distinct(initial.value) && forall((s: Store.T, q: Request.T) =>
    (distinct(s) ==> distinct(apply(s, q))) && onlyThat(s, q, apply(s, q)) && granted(s, q, apply(s, q))))

// ============================================================================
// Instantiation: realms, users, sessions and requests become concrete
// ============================================================================

final case class RealmId(name: String)
final case class UserAccount(realm: RealmId, username: String, passwordHash: String, enabled: Boolean, roles: List[String])
final case class Session(token: String, realm: RealmId, user: String)
final case class SessionStore(open: List[Session])

enum AuthRequest:
  /** A sign-in: the password arrives already hashed with the user's salt; `token` is a fresh random value the server drew. */
  case SignIn(realm: RealmId, user: String, passwordHash: String, token: String)
  case SignOut(realm: RealmId, token: String)

val users = Param[List[UserAccount]]("users",
  "every realm's users as loaded at start: username, salted password hash, whether enabled, realm roles")

/** Whether a user of the realm, enabled, has this password hash. */
val mayOpen = define { (realm: RealmId, user: String, hash: String) =>
  users.value.exists(a => a.realm == realm && a.username == user && a.passwordHash == hash && a.enabled)
}

/** No two open sessions share a token. */
val distinctTokens = define { (s: SessionStore) => s.open.forall(a => s.open.forall(b => (a.token == b.token) ==> (a == b))) }

/** What a request asks for, when it may be granted: a sign-in by an enabled user with their password and a
  * fresh token opens that session; a sign-out ends the realm's session of that token.
  */
val asked = define { (s: SessionStore, q: AuthRequest, t: SessionStore) =>
  q match
    case AuthRequest.SignIn(realm, user, hash, token) =>
      (mayOpen(realm, user, hash) && !s.open.exists(x => x.token == token)) ==> t.open.contains(Session(token, realm, user))
    case AuthRequest.SignOut(realm, token) => !t.open.exists(x => x.token == token && x.realm == realm)
}

/** What a request may change: a sign-in only adds its own session, if it may; a sign-out only removes the
  * realm's session of its token. No other session changes.
  */
val nothingElse = define { (s: SessionStore, q: AuthRequest, t: SessionStore) =>
  q match
    case AuthRequest.SignIn(realm, user, hash, token) =>
      s.open.forall(x => t.open.contains(x)) &&
        t.open.forall(x => s.open.contains(x) || (x == Session(token, realm, user) && mayOpen(realm, user, hash)))
    case AuthRequest.SignOut(realm, token) =>
      t.open.forall(x => s.open.contains(x)) && s.open.forall(x => t.open.contains(x) || (x.token == token && x.realm == realm))
}

val sessionTable = oneAtATime.instantiate[(SessionStore, AuthRequest) => SessionStore](
  "SessionTable",
  "The store is a list of open sessions (token, realm, user); a sign-in opens one for an enabled user whose password hash matches, under a fresh token; a sign-out ends its realm's session of the token.",
  why = "A session is what a token stands for, so a session holds its token, realm and user. Users are matched by realm and username: the same name in two realms is two users. A sign-out names its realm, so one realm's application cannot end another realm's sessions."
)(
  Store    := of[SessionStore],
  Request  := of[AuthRequest],
  initial  := SessionStore(Nil),
  distinct := ((s: SessionStore) => distinctTokens(s)),
  granted  := ((s: SessionStore, q: AuthRequest, t: SessionStore) => asked(s, q, t)),
  onlyThat := ((s: SessionStore, q: AuthRequest, t: SessionStore) => nothingElse(s, q, t))
)

// ============================================================================
// Contract: one request
// ============================================================================

val signInOut = sessionTable.contract[SessionStore, AuthRequest, SessionStore](
  "SignInOut",
  "A request keeps tokens distinct, opens a session only for an enabled user with their password, ends only its realm's session of its token, and does what it asks when it may.",
  why = "SessionTable, stated for one request, so each result of the running server is checked. A request that may not be granted leaves the store as it was."
)((s, q, t) => (distinctTokens(s) ==> distinctTokens(t)) && nothingElse(s, q, t) && asked(s, q, t))
  .examples(users.bind(List(UserAccount(RealmId("acme"), "alice", "h-alice", true, List("admin", "user")), UserAccount(RealmId("acme"), "bob", "h-bob", false, List("user")))))(
    expect(SessionStore(Nil), AuthRequest.SignIn(RealmId("acme"), "alice", "h-alice", "t1"), SessionStore(List(Session("t1", RealmId("acme"), "alice"))),
      "Alice signs in to acme with her password: a session under t1"),
    expect(SessionStore(Nil), AuthRequest.SignIn(RealmId("acme"), "bob", "h-bob", "t2"), SessionStore(Nil),
      "Bob is disabled: no session, even with his password"),
    expect(SessionStore(List(Session("t1", RealmId("acme"), "alice"))), AuthRequest.SignOut(RealmId("acme"), "t1"), SessionStore(Nil),
      "Alice signs out: her session ends"),
    reject(SessionStore(Nil), AuthRequest.SignIn(RealmId("acme"), "alice", "wrong", "t1"), SessionStore(List(Session("t1", RealmId("acme"), "alice"))),
      "a wrong password never opens a session"),
    reject(SessionStore(Nil), AuthRequest.SignIn(RealmId("globex"), "alice", "h-alice", "t1"), SessionStore(List(Session("t1", RealmId("globex"), "alice"))),
      "Alice is a user of acme, not of globex"),
    reject(SessionStore(List(Session("t1", RealmId("acme"), "alice"))), AuthRequest.SignOut(RealmId("globex"), "t1"), SessionStore(Nil),
      "globex cannot end acme's session"),
    reject(SessionStore(List(Session("t1", RealmId("acme"), "alice"))), AuthRequest.SignOut(RealmId("acme"), "t1"), SessionStore(List(Session("t1", RealmId("acme"), "alice"))),
      "a sign-out is never ignored"),
    reject(SessionStore(Nil), AuthRequest.SignIn(RealmId("acme"), "alice", "h-alice", "t1"), SessionStore(Nil),
      "Alice with her password is not turned away"))

/** One request: open the session when the user may sign in and the token is fresh; end the realm's session of a token. */
val step = define { (s: SessionStore, q: AuthRequest) =>
  q match
    case AuthRequest.SignIn(realm, user, hash, token) =>
      if mayOpen(realm, user, hash) && !s.open.exists(x => x.token == token) then SessionStore(s.open ++ List(Session(token, realm, user))) else s
    case AuthRequest.SignOut(realm, token) => SessionStore(s.open.filter(x => !(x.token == token && x.realm == realm)))
}
