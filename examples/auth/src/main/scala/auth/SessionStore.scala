package auth

/** The implementation: plain Scala, with any code and any data structures. It is attached to `DecisionContract` in
  * Auth.scala: the proofs above rest on that contract, and `check` tests this code against it, on cases generated from
  * the types (grant tables, session tables, tokens, paths) and on the examples; a change to this file shows on the
  * contract until the developer confirms it.
  */
final class SessionStore(grantTable: Set[Grant], tokens: String => Option[UserId]):
  def decide(token: String, path: Path): Option[UserId] =
    tokens(token).filter(u => grantTable.contains(Grant(u, path)))
