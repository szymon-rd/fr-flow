package auth

/** The implementation: plain Scala, with any code and any data structures. It is attached to
  * `DecisionContract` in Auth.scala; its examples run against it, and a change to this file
  * shows on the contract until the developer confirms it.
  */
final class SessionStore(grantTable: Set[Grant], tokens: String => Option[UserId]):
  def decide(token: String, path: Path): Option[UserId] =
    tokens(token).filter(u => grantTable.contains(Grant(u, path)))
