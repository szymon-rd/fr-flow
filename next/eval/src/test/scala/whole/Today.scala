package whole

import frflow.dsl.kb.FrModel

/** The examples' nodes as today's library has them (each FrModel's list under examples), by id, and the
  * FrModels written in the three kinds.
  */
object Today:
  val all: List[(String, FrModel)] = List("rooms" -> _root_.rooms.rooms,
    "auth" -> _root_.auth.knowledge, "keycloak" -> _root_.keycloak.knowledge, "crm" -> _root_.crm.knowledge,
    "sharing" -> _root_.sharing.knowledge)

  val rooms: Set[String] = Set("bookWhenFree", "answerWhenFree", "neverOverlap", "endsAfterStart", "bookingsOfTheRoom",
    "roomBookingsApart", "grantWhenFree", "grantWhenNoOverlap", "tableMatchesModel", "onlyBookingWrites", "oneAtATime",
    "startsEmpty", "requestsEndAfterStart")

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

  val sharing: Set[String] = Set("reach", "cover", "permission", "inTrash", "ownersShare", "accessFollowsShares",
    "invitationsAreOffers", "trashUntilGone", "housekeepingClearsOnlyTheEnded", "accessRequestsAreAsks",
    "ownersKeepTheirDocuments", "auditTrail", "noticesFollowChanges", "accessContract", "canViewContract",
    "canEditContract", "shareContract", "unshareContract", "moveContract", "inviteContract", "acceptContract",
    "withdrawContract", "trashContract", "restoreContract", "askContract", "approveContract", "declineContract",
    "chaseContract", "transferContract", "recordContract", "forgetContract", "announceContract", "warnContract",
    "tidyContract", "housekeepingJob", "deliveryJob", "invitationLifetime", "trashLifetime", "requestLifetime",
    "housekeepingPeriod", "inForceContract", "isOpenContract", "goneContract", "pendingContract",
    "reminderDueContract", "trashPurgedOnTime", "invitationsLapseOnTime", "requestsAnsweredOnTime",
    "endedStaysEnded", "clockNeverGoesBack", "housekeepingOnTime", "libraryKept", "transactions", "mailerKept",
    "clockKept", "handleContract", "serverWiring", "domainTypes")
