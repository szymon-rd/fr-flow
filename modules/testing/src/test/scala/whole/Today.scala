package whole

import frflow.dsl.kb.FrModel

/** The examples' nodes as today's library has them (each FrModel's list under examples), by id, and the
  * FrModels written in the three kinds.
  */
object Today:
  val all: List[(String, FrModel)] = List("rooms" -> _root_.rooms.rooms,
    "auth" -> _root_.auth.knowledge, "keycloak" -> _root_.keycloak.knowledge, "crm" -> _root_.crm.knowledge)

  /** Today's rooms as `reference/rooms` captured it (526fe35): seventeen nodes. */
  val rooms: Set[String] = Set("bookWhenFree", "acceptWhenFree", "bookedIsStored", "bookedAfterIsStored",
    "acceptedIsAnswered", "storeWhenFree", "answerWhenFree", "neverOverlap", "grantWhenFree", "bookingsOfTheRoom",
    "roomBookingsApart", "grantWhenNoOverlap", "tableMatchesModel", "onlyBookingWrites", "oneAtATime", "startsEmpty",
    "bookingsEndAfterStart")

  val auth: Set[String] = Set("accessExactly", "identities", "grantTable", "sessionTable", "requests",
    "tokenNamesHolder", "accessNeedsGrant", "grantLetsIn", "decisionContract", "inMemorySessions")

  val keycloak: Set[String] = Set("realmAccess", "noUnauthorizedAccess", "signedInAreAccepted", "onlyTheSignedIn",
    "disabledHaveNoAccess", "rolesAsGranted", "identities", "accounts", "signInHistory", "serverRun",
    "referenceTokens", "realmIsolation", "answersNameASession", "sessionsMirrorSignIns", "accountsAsAdministered",
    "oneSignInPerToken", "freshTokens", "handleRequest", "storeKeepsState", "introspect", "sessionLookup",
    "serviceWiring", "httpApi")

  val crm: Set[String] = Set("sharedCrm", "companies", "searches", "adding", "sharing", "crmRun",
    "storeMirrorsRequests", "visibility", "noCrossTenantRead", "searchesMatch", "readContract", "dealSearch",
    "recordsByQuery", "readSideWiring", "writesTakeEffect", "writesOnlyAsAsked", "recordsKept", "writeContract",
    "saveWrite", "storeEdits", "writeSideWiring", "sharesExpire", "tablesModel", "expiryJob", "expiryJobWiring",
    "httpApi")

