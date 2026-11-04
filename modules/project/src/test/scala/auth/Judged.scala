package auth

import frflow.project.Ported

/** What auth's port judges (`PortSuite`): each difference from today's in where a node sits and what it assumes, each
  * node standing apart from today's, and how each value provided where the code runs stands under owner §45 D.
  */
object Judged:
  /** Each difference from today's auth, with why the design makes it. */
  val differences: Map[String, (String, String)] = Map(
    "identities" -> ("gone" ->
      "it fixed two open types to UserId and Path, which the Declarations' types now say (owner §15)"),
    "tokensIssuedOnce" -> ("new" ->
      ("the session table is a list, so what today's function said, one user per token, is said of it (owner §40)")),
    "accessExactly" -> ("grantTable, sessionTable, requests are parts" ->
      ("today's definitions of its words are claims saying what each Declaration is, below the purpose it is stated " +
        "in (2.7)")),
    "tokenNamesHolder" -> ("assumes +tokensIssuedOnce" ->
      "its Lean takes what always holds of the session table, a value from outside (2.6, owner §21)"),
    "grantLetsIn" -> ("assumes +tokensIssuedOnce" ->
      "its Lean takes what always holds of the session table, a value from outside (2.6, owner §21)"),
    "decisionContract" -> ("assumes +tokensIssuedOnce" ->
      "its Lean takes what always holds of the session table, a value from outside (2.6, owner §21)"))

  /** Each value provided where the code runs, under owner §45 D, which names auth: its tables stay provided (§48). */
  val provided: Map[String, Ported.OnD] = Map("grants" -> Ported.OnD.Ruled("§48", table),
    "sessions" -> Ported.OnD.Ruled("§48", table))

  private def table = "auth's tables read in one moment stay provided: no statement of auth is about the state over " +
    "time (each holds of one decision, with no run, isConstant or history), so the value provided is the World's at " +
    "that moment; were one to compare two moments, they would move into the World then"

  /** Where each node stands apart from today, each for a reason the design gives. */
  val standings: Map[String, List[String]] = Map(
    // Gone: the types say it.
    "Identities" -> Nil,
    // New: trusted, what the session table issues.
    "TokensIssuedOnce" -> List("assumption", "assumed", "proven", ""),
    // Today's definitions, claims saying what each Declaration is (2.7): proven of what stands in them.
    "GrantTable" -> List("claim", "proven", "proven", ""),
    "SessionTable" -> List("claim", "proven", "proven", ""),
    "Requests" -> List("claim", "proven", "proven", ""),
    // A contract is a claim (owner §15).
    "DecisionContract" -> List("claim", "tested", "proven", "1000"),
    // Claims mentioning admit, tested against its Scala as well as proven from decisionContract (2.7).
    "TokenNamesHolder" -> List("claim", "tested", "proven", "1000"),
    "AccessNeedsGrant" -> List("claim", "tested", "proven", "1000"),
    "GrantLetsIn" -> List("claim", "tested", "proven", "1000"))
