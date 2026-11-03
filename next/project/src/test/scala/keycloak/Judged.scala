package keycloak

import frflow.project.Ported

/** What keycloak's port judges (`PortSuite`): each difference from today's in where a node sits and what it assumes,
  * each node standing apart from today's, and how each value provided where the code ran stands under owner §45 D.
  */
object Judged:
  /** Each difference from today's keycloak, with why the design makes it. */
  val differences: Map[String, (String, String)] = Map(
    "identities" -> ("gone" ->
      "it fixed four open types to realms and strings, which the Declarations' types now say (owner §15)"),
    "introspect" -> ("gone" -> "its claim is introspectAnswers, named apart from the Definition (owner §40)"),
    "introspectAnswers" -> ("new" -> "today's introspect, named apart from the Definition it is about (owner §40)"),
    "accountRoles" -> ("new" ->
      "today's accounts defined two words, enabled and rolesOf: a claim says what each Declaration is (2.7)"),
    "onlyTheSignedIn" -> ("signInHistory, referenceTokens are parts" -> words),
    "disabledHaveNoAccess" -> ("accounts, referenceTokens, introspectAnswers are parts" -> words),
    "rolesAsGranted" -> ("accountRoles, referenceTokens, introspectAnswers are parts" -> words),
    "signedInAreAccepted" -> ("accounts, accountRoles, signInHistory, referenceTokens, introspectAnswers are " +
      "parts; oneSignInPerToken no part" -> (words + "; and " + rule("oneSignInPerToken"))),
    "answersNameASession" -> ("introspectAnswers is a part; assumes +storeOneAtATime" -> (renamed + "; and " + runs)),
    "realmIsolation" -> ("introspectAnswers is a part; assumes +storeOneAtATime" -> (renamed + "; and " + runs)),
    "sessionsMirrorSignIns" -> ("freshTokens no part" -> rule("freshTokens")),
    "oneSignInPerToken" -> ("freshTokens no part; assumes +storeOnlyCode +storeOneAtATime +storeStarts" ->
      (rule("oneSignInPerToken itself, a rule of the store") + ", kept by the server's code, so it rests on the " +
        "store's premises; and " + rule("freshTokens"))),
    "serverRun" -> ("assumes +storeOnlyCode +storeOneAtATime +storeStarts" -> (premises + " (today's definition " +
      "over a provided state is a rule of the store, kept by the code)")),
    "freshTokens" -> ("assumes +storeOnlyCode +storeOneAtATime +storeStarts" -> (premises + " (today's assumption " +
      "over a provided history is a rule of the store, kept by the code given what the HTTP API hands it)")),
    "storeOnlyCode" -> ("new" -> "nothing but the code changes the store, the World's model of it (owner §31, §36)"),
    "storeOneAtATime" -> ("new" -> "runs on the store never interleave, an assumption of the model (owner §32)"),
    "storeStarts" -> ("new" -> "what the store starts in, which its rules rest on (2.6, Problem.NoStart)"),
    "storeLogs" -> ("new" -> ("what storing a request leaves, known only by what is assumed of it (G2): the state " +
      "stored, the request logged; the store's rules need it (Problem.LeavesUnsaid)")),
    "lookupKeeps" -> ("new" -> "what looking a token up leaves, as storeLogs is for storing (G2, LeavesUnsaid)"),
    "drawnTokens" -> ("new" -> ("what is trusted of each request the HTTP API hands the server: today's freshTokens " +
      "over the history, said of what enters it, so the history's rule is proven of the code")),
    "handedOneAtATime" -> ("new" -> "the requests are handed one at a time, an assumption of the inbox's model"),
    "loadedKept" -> ("new" -> ("the accounts as loaded, a field of the store no operation changes, kept (owner " +
      "§45 D, the coordinator's ruling: the configuration in the World, isConstant proven)")),
    "answersWhatItStores" -> ("new" -> ("the server is a program over its store now: the claim its code is checked " +
      "against, what the wiring did (CodeWithoutClaim)")))

  private def words = "today's definitions of the purpose's words are claims saying what each Declaration is, below " +
    "the steps they are used in (2.7), with today's introspect, renamed (owner §40)"
  private def renamed = "today's introspect, which refined and kept it, renamed (owner §40)"
  private def runs = "a claim about a program's runs rests on the store's runs being atomic (2.6)"
  private def rule(n: String) = s"$n is a rule of the store's state (owner §45 D: the history the World's), a " +
    "hypothesis of every statement reading the store, no part of its step (owner §27)"
  private def premises = "a rule of the store's state rests on what the store starts in, nothing but the code " +
    "changing it, and its runs one at a time (2.6)"

  /** Where each node stands apart from today, each for a reason the design gives. */
  val standings: Map[String, List[String]] = Map(
    // Gone: the types say it; and today's introspect, renamed.
    "Identities" -> Nil,
    "Introspect" -> Nil,
    // Today's definitions, claims saying what each Declaration is (2.7): proven of what stands in them.
    "Accounts" -> List("claim", "proven", "proven", ""),
    "AccountRoles" -> List("claim", "proven", "proven", ""),
    "SignInHistory" -> List("claim", "proven", "proven", ""),
    "ReferenceTokens" -> List("claim", "proven", "proven", ""),
    // Today's definition of what the server holds and assumption of fresh tokens, over provided values: rules of
    // the store now, the World's (owner §45 D), proven of the code that changes it (cover_, start_).
    "ServerRun" -> List("claim", "proven", "proven", ""),
    "FreshTokens" -> List("claim", "proven", "proven", ""),
    // A contract or an invariant is a claim (owner §15); today's introspect named apart (owner §40), proven of
    // the introspection's program now, no longer plain Scala tested.
    "HandleRequest" -> List("claim", "proven", "proven", ""),
    "RealmIsolation" -> List("claim", "proven", "proven", ""),
    "IntrospectAnswers" -> List("claim", "proven", "proven", ""),
    // The store's storing and index, operations known only by what is assumed of them (G2): their Scala tested
    // against it on the store's generated runs, today's 1,000, reported beside storeOnlyCode.
    "SessionLookup" -> List("assumption", "assumed", "proven", ""),
    "StoreKeepsState" -> List("assumption", "assumed", "proven", ""),
    "StoreLogs" -> List("assumption", "assumed", "proven", ""),
    "LookupKeeps" -> List("assumption", "assumed", "proven", ""),
    "StoreOnlyCode" -> List("assumption", "assumed", "", "1000"),
    "StoreOneAtATime" -> List("assumption", "assumed", "", ""),
    "StoreStarts" -> List("assumption", "assumed", "", ""),
    // What the HTTP API hands the server: trusted (its runs read the store, which the inbox's own runs lack).
    "DrawnTokens" -> List("assumption", "assumed", "proven", ""),
    "HandedOneAtATime" -> List("assumption", "assumed", "", ""),
    // New claims of the server's programs.
    "LoadedKept" -> List("claim", "proven", "proven", ""),
    "AnswersWhatItStores" -> List("claim", "proven", "proven", ""))

  /** None now: the history, the state now and the accounts as loaded are the server's store's, the World's. */
  val provided: Map[String, Ported.OnD] = Map.empty
