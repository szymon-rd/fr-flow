package keycloak

import frflow.*

// ============================================================================
// Design: how the proven core runs
// ============================================================================

val serviceWiring = Node.design("Every request reaches the store through service, one at a time: a sign-in, " +
    "sign-out or administrator's change runs handleRequest's code on the stored state, which stores its result " +
    "through storeKeepsState; an introspection runs introspect's code on the state the store holds.")(
  "src/main/scala/keycloak/Wiring.scala")
  .refines(handleRequest, Introspection.introspect)

val httpApi = Node.design("The HTTP API serves Keycloak's token, introspection and logout endpoints for each realm, " +
    "and lets an administrator enable or disable a user; it hashes the password with the user's salt and draws " +
    "each token from a secure random source before calling the wiring.")(
  "src/main/scala/keycloak/Server.scala")
  .refines(serviceWiring, freshTokens)

val knowledge = KnowledgeBase("Keycloak")(realmAccess, noUnauthorizedAccess, signedInAreAccepted, onlyTheSignedIn,
  disabledHaveNoAccess, rolesAsGranted, accounts, accountRoles, signInHistory, serverRun, referenceTokens,
  realmIsolation, answersNameASession, sessionsMirrorSignIns, accountsAsAdministered, oneSignInPerToken, freshTokens,
  handleRequest, storeKeepsState, Introspection.introspect, sessionLookup, serviceWiring, httpApi)
  .implementProvided(seed, history, state)
  .implementProven(step)(handle)
  .implementTested(record)(_ => (q, after) => SessionDb.holding(after).storeAfter(q, after))
  .implementTested(lookup)(env => (realm, token) => SessionDb.holding(env(state)).find(realm, token))
  .implementTested(introspect, lookup, account)(env => introspection(env(lookup), env(account)))
