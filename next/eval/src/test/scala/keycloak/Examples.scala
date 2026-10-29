package keycloak

import frflow.*

// Today's examples, one class per node they were written on, each giving the state the server holds: checked
// against the code in Scala only (owner §18).

// ============================================================================
// Accounts the examples use
// ============================================================================

val acme = RealmId("acme")
val globex = RealmId("globex")
val alice = UserAccount(acme, "alice", "h-alice", true, List("admin", "user"))
val bob = UserAccount(acme, "bob", "h-bob", false, List("user"))
val carol = UserAccount(globex, "carol", "h-carol", true, List("viewer"))
val loaded = List(alice, bob)
val bobOn = UserAccount(acme, "bob", "h-bob", true, List("user"))
val atStart = List(alice, bobOn, carol)

/** Alice and Bob sign in to acme, Carol to globex; Bob is disabled; Alice signs in again, and signs out of that
  * session.
  */
val events = List(
  AuthRequest.SignIn(acme, "alice", "h-alice", "t1"),
  AuthRequest.SignIn(acme, "bob", "h-bob", "t2"),
  AuthRequest.SignIn(globex, "carol", "h-carol", "t4"),
  AuthRequest.SetEnabled(acme, "bob", false),
  AuthRequest.SignIn(acme, "alice", "h-alice", "t3"),
  AuthRequest.SignOut(acme, "t3"))

/** What the server holds after `events`, from `atStart`: Bob disabled, the sessions of t1, t2 and t4 open. */
val afterEvents = ServerState(List(alice, bob, carol),
  List(Session("t1", acme, "alice"), Session("t2", acme, "bob"), Session("t4", globex, "carol")))

/** The server after `events`: what each example of the introspection and the index is given. */
private val replayed = List(history := events, seed := atStart, state := afterEvents)

class IntrospectExamples extends FrFlowExamples(knowledge):
  example("Alice's token at acme: accepted as hers, with her roles", replayed*):
    introspect(acme, "t1") is Some(Claims(acme, "alice", List("admin", "user")))
  example("Carol's token at globex: accepted as hers", replayed*):
    introspect(globex, "t4") is Some(Claims(globex, "carol", List("viewer")))
  example("acme's token is not good at globex", replayed*):
    introspect(globex, "t1") is None
  example("Bob was disabled after signing in: his token is no longer accepted", replayed*):
    introspect(acme, "t2") is None
  example("Alice signed out with t3", replayed*):
    introspect(acme, "t3") is None
  example("a token no sign-in got", replayed*):
    introspect(acme, "t9") is None
  example("a token is never good in another realm", replayed*):
    (introspect(globex, "t1") is Some(Claims(globex, "alice", List("admin", "user")))) is false
  example("nor is globex's token good at acme", replayed*):
    (introspect(acme, "t4") is Some(Claims(acme, "carol", List("viewer")))) is false
  example("a disabled user's token is never accepted", replayed*):
    (introspect(acme, "t2") is Some(Claims(acme, "bob", List("user")))) is false
  example("a token signed out with is never accepted again", replayed*):
    (introspect(acme, "t3") is Some(Claims(acme, "alice", List("admin", "user")))) is false
  example("roles are never made up", replayed*):
    (introspect(acme, "t1") is Some(Claims(acme, "alice", List("admin", "user", "owner")))) is false
  example("Alice's token is not turned away", replayed*):
    (introspect(acme, "t1") is None) is false

class LookupExamples extends FrFlowExamples(knowledge):
  example("acme's session of t1", replayed*):
    lookup(acme, "t1") is Some(Session("t1", acme, "alice"))
  example("the store keeps sessions per realm: none of globex under t1", replayed*):
    lookup(globex, "t1") is None
  example("Alice signed out with t3: its session is gone", replayed*):
    lookup(acme, "t3") is None
  example("a session the store holds is never lost", replayed*):
    (lookup(acme, "t1") is None) is false
  example("another realm's session is never returned", replayed*):
    (lookup(globex, "t1") is Some(Session("t1", acme, "alice"))) is false

/** Alice's sign-in with t1, and the state with her session under it. */
private val aliceIn = AuthRequest.SignIn(acme, "alice", "h-alice", "t1")
private val withAlice = ServerState(loaded, List(Session("t1", acme, "alice")))
private val noSession = ServerState(loaded, Nil)

class StoreExamples extends FrFlowExamples(knowledge):
  example("Alice's new session is stored, and read back"):
    record(aliceIn, withAlice) is withAlice
  example("after her sign-out, no session is stored"):
    record(AuthRequest.SignOut(acme, "t1"), noSession) is noSession
  example("a session the store dropped is seen"):
    (record(aliceIn, withAlice) is noSession) is false

class RequestExamples extends FrFlowExamples(knowledge):
  example("Alice signs in to acme with her password: a session under t1"):
    step(noSession, aliceIn) is withAlice
  example("Bob is disabled: no session, even with his password"):
    step(noSession, AuthRequest.SignIn(acme, "bob", "h-bob", "t2")) is noSession
  example("Alice signs out: her session ends"):
    step(withAlice, AuthRequest.SignOut(acme, "t1")) is noSession
  example("an administrator disables Alice; her session stays, and is no longer accepted"):
    step(withAlice, AuthRequest.SetEnabled(acme, "alice", false)) is
      ServerState(List(alice.copy(enabled = false), bob), List(Session("t1", acme, "alice")))
  example("a wrong password never opens a session"):
    (step(noSession, AuthRequest.SignIn(acme, "alice", "wrong", "t1")) is withAlice) is false
  example("Alice is a user of acme, not of globex"):
    (step(noSession, AuthRequest.SignIn(globex, "alice", "h-alice", "t1")) is
      ServerState(loaded, List(Session("t1", globex, "alice")))) is false
  example("a token an open session holds never opens another"):
    (step(ServerState(List(alice, bobOn), List(Session("t1", acme, "alice"))),
      AuthRequest.SignIn(acme, "bob", "h-bob", "t1")) is
      ServerState(List(alice, bobOn), List(Session("t1", acme, "alice"), Session("t1", acme, "bob")))) is false
  example("globex cannot end acme's session"):
    (step(withAlice, AuthRequest.SignOut(globex, "t1")) is noSession) is false
  example("a sign-out is never ignored"):
    (step(withAlice, AuthRequest.SignOut(acme, "t1")) is withAlice) is false
  example("Alice with her password is not turned away"):
    (step(noSession, aliceIn) is noSession) is false
  example("an administrator's change is never ignored"):
    (step(noSession, AuthRequest.SetEnabled(acme, "bob", true)) is noSession) is false
