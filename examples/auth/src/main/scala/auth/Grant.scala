package auth

import frflow.*

/** A grant: the user is allowed the path. */
final case class Grant(user: UserId, path: Path) derives LeanType

/** The grant table, and what being authorized is in terms of it. */
object Grant:
  val grants = Definition[List[Grant]]("the grant table as stored when the request is decided")

  /** A grant names the user and the path. */
  val grantFor = define { (u: Term[UserId], p: Term[Path]) => grants.exists(g => g === make[Grant](u, p)) }

  val grantTable = Node.claim("A user is authorized for a path exactly when a grant names that user and that path.")(
    forall((u: Term[UserId], p: Term[Path]) => Auth.authorized(u, p) === grantFor(u, p)))
    .refines(Auth.accessExactly)
