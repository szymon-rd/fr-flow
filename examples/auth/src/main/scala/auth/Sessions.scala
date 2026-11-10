package auth

import frflow.*

/** The session table: each token with the user it was issued to at login. */
final case class Sessions(open: List[Session]) derives LeanType

/** The session table as stored, what is trusted of it, and what being signed in is in terms of it. */
object Sessions:
  val sessions = Definition[Sessions](
    "the session table as stored when the request is decided: a token to the user it was issued to at login")

  /** The user the token was issued to, if any. */
  val holderOf = define { (t: Term[String]) => sessions.open.find(s => s.token === t).map(s => s.user) }

  val tokensIssuedOnce = Node.assumption("The session table issues each token to one user.")(
    always[Sessions](s => s.open.pairwise((a, b) => a.token =!= b.token)))

  val sessionTable = Node.claim("A user is signed in exactly when some session token was issued to them.")(
    forall((u: Term[UserId]) => Auth.signedIn(u) === sessions.open.exists(s => s.user === u)))
    .refines(Auth.accessExactly)

  /** The session table is provided where the code runs. */
  def implemented(model: FrModel): FrModel = model.implementProvided(sessions)
