package keycloak

import frflow.*

/** The production wiring, owned as a design decision: a change to it is reviewed. */
val serviceWiring = signInOut.design(
  "ServiceWiring",
  "Sign-ins, sign-outs and introspections run through service, which checks every result against SignInOut or Introspect, on one in-memory session store.",
  why = "Every path to the sessions must go through service; keeping the wiring in one governed file makes a change to it visible. One process holds the store, so a sign-out is seen by the next introspection at once."
)("src/main/scala/keycloak/Wiring.scala")
  .exempt(realmIsolation, "it returns what SignInOut and Introspect return, which are checked against the rule")

/** The HTTP API, owned as a design decision: Keycloak's endpoints, answered by the wiring. */
val httpApi = introspectContract.design(
  "HttpApi",
  "The HTTP API serves Keycloak's token, introspection and logout endpoints for each realm, and lets an administrator enable or disable a user; it hashes the password with the user's salt and draws each token from a secure random source before calling the wiring.",
  why = "Applications already speak Keycloak's OpenID Connect endpoints, so the paths and answers are Keycloak's. Hashing and drawing tokens happen here, outside the proven core (Not modelled): a 256-bit random token is distinct from every open one in practice, and the core refuses one that is not."
)("src/main/scala/keycloak/Server.scala")
  .exempt(realmIsolation, "it returns only what Introspect returns, which keeps the rule")

val knowledge = KnowledgeBase("Keycloak", idea = "IDEA.md")(
  sessions, tokenCheck, oneAtATime, sessionTable, referenceTokens, signInOut, introspectContract, realmIsolation, sessionLookup, serviceWiring, httpApi)
  .implementProven(sessionLookup)(storedSession, (realm, token) => sessionDb.value.find(realm, token))
  .implementProven(signInOut)(step)
  .implementProven(introspectContract)(introspect)

@main def keycloakCli(args: String*): Unit = sys.exit(knowledge.cli(args, root = "examples/keycloak"))
