package auth

/** How the system runs: the tables are loaded once into memory, in one process, and every request
  * is decided by the registered implementation, with each result checked against the contract.
  * Governed by the design decision `InMemorySessions`.
  */
def service(grantTable: List[Grant], tokens: Map[String, UserId]): (String, Path) => Option[UserId] =
  knowledge.service(decisionContract)(grants.bind(grantTable), sessions.bind(t => tokens.get(t)))
