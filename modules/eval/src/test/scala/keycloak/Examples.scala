package keycloak

import frflow.*

// Today's examples. Those of the step, a function, are examples (owner §18), tried against the claims in Lean too.
// Those of the introspection, the index and the store were given the state the server holds; the server's state is
// the World's now (owner §45 D) and an example reads no world (2.10), so each is a run of the code on a store
// holding it, in production's interpreter (`PortSuite`).

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

/** The store after `events`: what each of today's examples of the introspection and the index was given. */
val replayed = Stored(atStart, afterEvents, events)

/** One of today's examples of a run: what it says, the run's inputs, what it gives, and whether it gives that
  * (`holds`) or never does.
  */
final case class RunExample[I, O](says: String, inputs: I, gives: O, holds: Boolean = true)

private val aliceClaims = Some(Claims(acme, "alice", List("admin", "user")))

/** Today's examples of the introspection, on the store holding `replayed`. */
val introspections: List[RunExample[(RealmId, String), Option[Claims]]] = List(
  RunExample("Alice's token at acme: accepted as hers, with her roles", (acme, "t1"), aliceClaims),
  RunExample("Carol's token at globex: accepted as hers", (globex, "t4"),
    Some(Claims(globex, "carol", List("viewer")))),
  RunExample("acme's token is not good at globex", (globex, "t1"), None),
  RunExample("Bob was disabled after signing in: his token is no longer accepted", (acme, "t2"), None),
  RunExample("Alice signed out with t3", (acme, "t3"), None),
  RunExample("a token no sign-in got", (acme, "t9"), None),
  RunExample("a token is never good in another realm", (globex, "t1"),
    Some(Claims(globex, "alice", List("admin", "user"))), holds = false),
  RunExample("nor is globex's token good at acme", (acme, "t4"), Some(Claims(acme, "carol", List("viewer"))),
    holds = false),
  RunExample("a disabled user's token is never accepted", (acme, "t2"), Some(Claims(acme, "bob", List("user"))),
    holds = false),
  RunExample("a token signed out with is never accepted again", (acme, "t3"), aliceClaims, holds = false),
  RunExample("roles are never made up", (acme, "t1"), Some(Claims(acme, "alice", List("admin", "user", "owner"))),
    holds = false),
  RunExample("Alice's token is not turned away", (acme, "t1"), None, holds = false))

/** Today's examples of the index, on the store holding `replayed`. */
val lookups: List[RunExample[(RealmId, String), Option[Session]]] = List(
  RunExample("acme's session of t1", (acme, "t1"), Some(Session("t1", acme, "alice"))),
  RunExample("the store keeps sessions per realm: none of globex under t1", (globex, "t1"), None),
  RunExample("Alice signed out with t3: its session is gone", (acme, "t3"), None),
  RunExample("a session the store holds is never lost", (acme, "t1"), None, holds = false),
  RunExample("another realm's session is never returned", (globex, "t1"), Some(Session("t1", acme, "alice")),
    holds = false))

/** Alice's sign-in with t1, and the state with her session under it. */
private val aliceIn = AuthRequest.SignIn(acme, "alice", "h-alice", "t1")
private val withAlice = ServerState(loaded, List(Session("t1", acme, "alice")))
private val noSession = ServerState(loaded, Nil)

/** Today's examples of the store, each on a store holding the accounts loaded and nothing else: the request and
  * the state stored, and what is read back.
  */
val stores: List[RunExample[(AuthRequest, ServerState), ServerState]] = List(
  RunExample("Alice's new session is stored, and read back", (aliceIn, withAlice), withAlice),
  RunExample("after her sign-out, no session is stored", (AuthRequest.SignOut(acme, "t1"), noSession), noSession),
  RunExample("a session the store dropped is seen", (aliceIn, withAlice), noSession, holds = false))

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
