package auth

import frflow.*

/** How the system runs: the tables are loaded once into memory, in one process, and every request is decided by
  * `admit`'s code, given the tables; nothing checks a call in production.
  */
object Server:
  val inMemorySessions = Node.design(
    "One process decides every request, from the sessions and grants it holds in memory.")(
    "src/main/scala/auth/Server.scala").refines(Admission.decisionContract)

  def service(grantTable: List[Grant], tokens: Sessions): (String, Path) => Option[UserId] =
    Auth.model.code(Admission.admit)(Grant.grants := grantTable, Sessions.sessions := tokens)
