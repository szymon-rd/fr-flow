package keycloak

import frflow.*

// ============================================================================
// Invariant: realms are isolated, in every answer to an application
// ============================================================================

final case class Claims(realm: RealmId, user: String, roles: List[String])

/** One rule for every answer to an application, stated once: claims are only ever of the realm asking. */
val realmIsolation = Node.invariant[RealmId, Claims](
  "RealmIsolation",
  "No application is ever shown claims of a realm other than its own.",
  why = "The idea says a token is only ever good in the realm that issued it. Stated once over every answer the server gives, so a new endpoint (user info, an admin view of sessions) must keep it or say why not."
)((asking, c) => c.realm == asking)
