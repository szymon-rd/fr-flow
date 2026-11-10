package auth

import frflow.*

/** Access control: a user gets access to a resource exactly when they are signed in and authorized for it.
  *
  * The purpose is stated over Declarations, known only by what the statements say of them; the parts below say what
  * each is in the code: the grant table (`Grant`), the session table (`Sessions`) and the decision on a request
  * (`Admission`).
  */
object Auth:
  val access = Declaration[(UserId, Path) => Boolean]("whether the system lets the user access the resource")

  val authorized = Declaration[(UserId, Path) => Boolean](
    "whether the user is allowed the resource, by whatever rule the system adopts")

  val signedIn = Declaration[UserId => Boolean]("whether the user has signed in, so can present who they are")

  val accessExactly = Node.claim(
      "A user gets access to a resource exactly when they are signed in and authorized for it.")(
    forall((u: Term[UserId], r: Term[Path]) => access(u, r) === (signedIn(u) && authorized(u, r))))

  /** Auth's FrModel: every node, and what gives each Definition its meaning. Lazy, because it names the nodes below
    * the root, which name the root.
    */
  lazy val model: FrModel = FrModel("Auth")(accessExactly, Grant.grantTable, Sessions.sessionTable,
    Admission.requests, Admission.tokenNamesHolder, Admission.accessNeedsGrant, Admission.grantLetsIn,
    Admission.decisionContract, Server.inMemorySessions, Sessions.tokensIssuedOnce)
    .implementProvided(Grant.grants, Sessions.sessions)
    .implementTested(Admission.admit)(env => Admission(env(Grant.grants), env(Sessions.sessions)).decide)
