package keycloak

import frflow.*

// ============================================================================
// Design: how the proven core runs
// ============================================================================

val serviceWiring = Node.design("Every request reaches the store through service, one at a time: a sign-in, sign-out or administrator's change runs HandleRequest's code on the stored state, which stores its result through StoreKeepsState; an introspection runs Introspect's code on the state the store holds.",
  why = "The proofs are about a server whose state is its requests applied in turn (ServerRun): every path to the store must go through service, and keeping the wiring in one governed file makes a change to it visible. One process holds the store, so a sign-out or a disabled user is seen by the next introspection at once."
)("src/main/scala/keycloak/Wiring.scala")
  .refines(handleRequest, Introspection.introspect)
  .exempt(realmIsolation, "it returns what Introspect returns, which keeps the rule, and stored states, which hold no claims")

val httpApi = Node.design("The HTTP API serves Keycloak's token, introspection and logout endpoints for each realm, and lets an administrator enable or disable a user; it hashes the password with the user's salt and draws each token from a secure random source before calling the wiring.",
  why = "Applications already speak Keycloak's OpenID Connect endpoints, so the paths and answers are Keycloak's. Hashing and drawing tokens happen here, outside the proven core (Not modelled): 256 random bits per token is what FreshTokens trusts, and the core refuses a token an open session holds."
)("src/main/scala/keycloak/Server.scala")
  .refines(serviceWiring, freshTokens)
  .exempt(realmIsolation, "it returns only what Introspect returns, which keeps the rule")

val knowledge = FrModel("Keycloak", idea = "IDEA.md")(
  realmAccess, noUnauthorizedAccess, signedInAreAccepted, onlyTheSignedIn, disabledHaveNoAccess, rolesAsGranted,
  identities, accounts, signInHistory, serverRun, referenceTokens,
  realmIsolation, answersNameASession, sessionsMirrorSignIns, accountsAsAdministered, oneSignInPerToken, freshTokens,
  handleRequest, storeKeepsState, Introspection.introspect, sessionLookup, serviceWiring, httpApi)
  .implementProven(storeKeepsState)(storedAs, (q, t) => sessionDb.value.storeAfter(q, t))
  .implementProven(sessionLookup)(storedSession, (realm, token) => sessionDb.value.find(realm, token))
  .implementProven(handleRequest)(handle)
  .implementTested(Introspection.introspect, lookup)(introspection)

object keycloakCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/keycloak", extensions = List(frflow.agent.Agent))
