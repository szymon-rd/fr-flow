package keycloak

import cats.syntax.all.*
import frflow.*

/** Stores as the server leaves them, for the tests' runs of its store's operations: what the store's rules say
  * (`serverRun`, `freshTokens`), in plain Scala. The accounts loaded and some requests drawn, the sign-ins carrying a
  * token an earlier one did dropped, each request handled in turn as `next` does.
  */
object Replay:
  /** The store after the requests, from the accounts loaded and no session. */
  def stored(loaded: List[UserAccount], asked: List[AuthRequest]): Stored =
    val log = asked.foldLeft(List.empty[AuthRequest])((done, q) => if fresh(done, q) then done :+ q else done)
    Stored(loaded, log.foldLeft(ServerState(loaded, Nil))(next), log)

  private def token(q: AuthRequest): Option[String] = q match
    case AuthRequest.SignIn(_, _, _, t) => Some(t)
    case _                              => None

  private def fresh(done: List[AuthRequest], q: AuthRequest): Boolean =
    token(q).forall(t => !done.exists(p => token(p).contains(t)))

  private def next(s: ServerState, q: AuthRequest): ServerState = q match
    case AuthRequest.SetEnabled(r, u, on) => s.copy(accounts = s.accounts.map(a =>
        if a.realm == r && a.username == u then a.copy(enabled = on) else a))
    case AuthRequest.SignOut(r, t)        => s.copy(sessions = s.sessions.filterNot(x => x.token == t && x.realm == r))
    case AuthRequest.SignIn(r, u, h, t)   =>
      val grants = s.accounts.find(a => a.realm == r && a.username == u).exists(a => a.enabled && a.passwordHash == h)
      if grants && !s.sessions.exists(_.token == t) then s.copy(sessions = s.sessions :+ Session(t, r, u)) else s

  /** Stores as the server's requests leave them. */
  val stores: Gen[Stored] = (for
    loaded <- Gens.derived[List[UserAccount]]
    asked  <- Gens.derived[List[AuthRequest]]
  yield stored(loaded, asked)).describedAs("stores as the server's requests leave them")
