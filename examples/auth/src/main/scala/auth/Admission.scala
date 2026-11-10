package auth

import frflow.*
import auth.Grant.grantFor
import auth.Sessions.{holderOf, sessions, tokensIssuedOnce}

/** The decision on a request, as plain Scala over the tables loaded into memory: the token's holder is admitted when
  * a grant names them and the path.
  */
final class Admission(grantTable: List[Grant], tokens: Sessions):
  private val granted = grantTable.toSet
  private val holders = tokens.open.map(s => s.token -> s.user).toMap

  def decide(token: String, path: Path): Option[UserId] = holders.get(token).filter(u => granted(Grant(u, path)))

/** The decision's contract: on whose behalf a request is admitted, and what every call must satisfy. */
object Admission:
  val admit = Definition[(String, Path) => Option[UserId]](
    "the system's decision on a request (a token and a path): the user it is admitted on behalf of, if any")

  /** The token's holder has a grant for the path. */
  val holderGranted = define { (t: Term[String], p: Term[Path]) => holderOf(t).exists(u => grantFor(u, p)) }

  /** Some session's token is admitted for the path on the user's behalf. */
  val admittedTo = define { (u: Term[UserId], p: Term[Path]) =>
    sessions.open.exists(s => admit(s.token, p) === some(u)) }

  val requests = Node.claim(
      "A user has access to a path exactly when some request for it is admitted on their behalf.")(
    forall((u: Term[UserId], p: Term[Path]) => Auth.access(u, p) === admittedTo(u, p)))
    .refines(Auth.accessExactly)

  val tokenNamesHolder = Node.claim("A request is admitted only on behalf of the user its token was issued to.")(
    forall((t: Term[String], p: Term[Path]) => admit(t, p).forall(u => holderOf(t) === some(u))))
    .refines(Auth.accessExactly)
    .assuming(tokensIssuedOnce)

  val accessNeedsGrant = Node.claim(
      "A request is admitted on behalf of a user only if a grant names that user and the path.")(
    forall((t: Term[String], p: Term[Path]) => admit(t, p).forall(u => grantFor(u, p))))
    .refines(Auth.accessExactly)

  val grantLetsIn = Node.claim(
      "A request whose token's holder has a grant for the path is admitted on the holder's behalf.")(
    forall((t: Term[String], p: Term[Path]) => holderGranted(t, p) implies (admit(t, p) === holderOf(t))))
    .refines(Auth.accessExactly)
    .assuming(tokensIssuedOnce)

  val decisionContract = Node.claim(
      "A request is admitted on behalf of its token's holder exactly when they have a grant for the path.")(
    forall((t: Term[String], p: Term[Path]) =>
      admit(t, p) === when(holderGranted(t, p))(holderOf(t)).otherwise(none[UserId])))
    .refines(tokenNamesHolder, accessNeedsGrant, grantLetsIn)
    .assuming(tokensIssuedOnce)
