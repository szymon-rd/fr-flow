package keycloak

import frflow.*

// ============================================================================
// Design: how the proven core runs
// ============================================================================

// serve runs handleRequest's step on the state the store holds, and stores it with the request.
val serviceWiring = Node.design("The server runs serve on its store for each request the HTTP API hands it.")(
  "src/main/scala/keycloak/Wiring.scala")
  .refines(handleRequest)

val introspectionWiring = Node.design("The server runs introspect on its store for each introspection.")(
  "src/main/scala/keycloak/Wiring.scala")
  .refines(introspectAnswers)

// The token, introspection, logout and user administration endpoints.
val httpApi = Node.design("The HTTP API serves Keycloak's endpoints for each realm.")(
  "src/main/scala/keycloak/Server.scala")
  .refines(serviceWiring)

val saltedPasswords = Node.design("The HTTP API hashes each password with the user's salt before handing the " +
    "sign-in to the server.")(
  "src/main/scala/keycloak/Server.scala")
  .refines(serviceWiring)

val randomTokens = Node.design("The HTTP API draws each token from a secure random source.")(
  "src/main/scala/keycloak/Server.scala")
  .refines(drawnTokens)

val answersWhatItStores = Node.claim("The server answers each request it handles with the state it stores.")(
  serve.result === serverStore.in(serve.after).state)
  .assuming(storeOneAtATime, handedOneAtATime)

/** What the inbox hands the tests' runs when no request waits, so each run ends (`HttpInbox.nextOr`). */
val idleRequest: AuthRequest = AuthRequest.SignOut(RealmId(""), "")

/** The FrModel's code, apart from its nodes: a variant keeps all but one. */
def withCode(kb: FrModel): FrModel = kb
  .implementProven(step)(next)
  .implementProven(serve)(serving)
  .implementProven(introspect)(introspecting)
  .implementTested(load, logged, record, lookup)(start = SessionDb.holding, observe = _.stored)(d =>
    (d.load, d.logged, d.record, d.lookup))
  .implementTested(nextRequest)(start = HttpInbox.holding, observe = _.left)(i => Tuple1(i.nextOr(idleRequest)))
  .withGenerator(Replay.stores)

val knowledge = withCode(FrModel("Keycloak")(realmAccess, noUnauthorizedAccess, signedInAreAccepted,
  onlyTheSignedIn, disabledHaveNoAccess, rolesAsGranted, accounts, accountRoles, signInHistory, serverRun,
  referenceTokens, realmIsolation, answersNameASession, sessionsMirrorSignIns, accountsAsAdministered,
  oneSignInPerToken, freshTokens, drawnTokens, handleRequest, requestSetsAccounts, endedSessionsClose,
  unendedSessionsStay, grantedSessionOpens, noOtherSessionOpens, storeKeepsState, storeHoldsState, storeAppendsLog,
  storeKeepsLoaded, introspectAnswers, answersOnlyEnabled, answersWithRoles, answersTheSession, lookupOnlyHeld,
  lookupFindsHeld, lookupKeeps, storeOnlyCode, storeOneAtATime, storeStarts, loadedKept, answersWhatItStores,
  handedOneAtATime,
  serviceWiring, introspectionWiring, httpApi, saltedPasswords, randomTokens))
