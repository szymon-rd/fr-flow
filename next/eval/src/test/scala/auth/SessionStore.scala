package auth

/** The implementation: plain Scala, with any code and any data structures. It gives `admit` its meaning (`Auth.scala`),
  * tested against every claim on `admit` on generated grant and session tables, tokens and paths.
  */
final class SessionStore(grantTable: List[Grant], tokens: Sessions):
  private val granted = grantTable.toSet
  private val holders = tokens.open.map(s => s.token -> s.user).toMap

  def decide(token: String, path: Path): Option[UserId] = holders.get(token).filter(u => granted(Grant(u, path)))
