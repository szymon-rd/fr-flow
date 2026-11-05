package keycloak

import frflow.*

// ============================================================================
// Design: how the proven core runs
// ============================================================================

val serviceWiring = Node.design("The server takes each request the HTTP API hands it, one at a time, and runs " +
    "serve's code on its store: handleRequest's step on the state it holds, stored with the request; an " +
    "introspection runs introspect's code on the store.")(
  "src/main/scala/keycloak/Wiring.scala")
  .refines(handleRequest, introspectAnswers)

val httpApi = Node.design("The HTTP API serves Keycloak's token, introspection and logout endpoints for each realm, " +
    "and lets an administrator enable or disable a user; it hashes the password with the user's salt and draws " +
    "each token from a secure random source before handing the request to the server.")(
  "src/main/scala/keycloak/Server.scala")
  .refines(serviceWiring, drawnTokens)

val answersWhatItStores = Node.claim("The server answers each request it handles with the state it stores.")(
  serve.result === serverStore.in(serve.after).state)
  .assuming(storeOneAtATime, handedOneAtATime)

/** The FrModel's code, apart from its nodes: a variant keeps all but one. */
def withCode(kb: FrModel): FrModel = kb
  .implementProven(step)(next)
  .implementProven(serve)(serving)
  .implementProven(introspect)(introspecting)
  .implementTested(load, logged, record, lookup)(start = SessionDb.holding, observe = _.stored)(d =>
    (d.load, d.logged, d.record, d.lookup))
  .implementTested(nextRequest)(start = HttpInbox.holding, observe = _.left)(i => Tuple1(i.next))
  .withGenerator(Replay.stores)

val knowledge = withCode(FrModel("Keycloak")(realmAccess, noUnauthorizedAccess, signedInAreAccepted,
  onlyTheSignedIn, disabledHaveNoAccess, rolesAsGranted, accounts, accountRoles, signInHistory, serverRun,
  referenceTokens, realmIsolation, answersNameASession, sessionsMirrorSignIns, accountsAsAdministered,
  oneSignInPerToken, freshTokens, drawnTokens, handleRequest, storeKeepsState, storeLogs, introspectAnswers,
  sessionLookup, lookupKeeps, storeOnlyCode, storeOneAtATime, storeStarts, loadedKept, answersWhatItStores,
  handedOneAtATime,
  serviceWiring, httpApi))
