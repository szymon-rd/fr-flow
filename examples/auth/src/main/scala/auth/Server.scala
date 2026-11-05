package auth

import frflow.*

/** How the system runs: the tables are loaded once into memory, in one process, and every request is decided by
  * `admit`'s code, given the tables (`knowledge.code`); nothing checks a call in production. Governed by the design
  * decision `inMemorySessions`.
  */
def service(grantTable: List[Grant], tokens: Sessions): (String, Path) => Option[UserId] =
  knowledge.code(admit)(grants := grantTable, sessions := tokens)
