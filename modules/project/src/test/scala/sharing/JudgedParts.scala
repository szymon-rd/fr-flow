package sharing

/** What making every statement of sharing small changed against today's (`Judged`, `PortSuite`): each composite node a
  * parent of its smaller statements, one fact each, which together say what it said; the World's rules one fact each.
  */
object JudgedParts:
  /** Each new part, by the node of today's (or of the port's) it was split from. */
  val newParts: Map[String, String] = Map(
    "viewFollowsShares" -> "accessFollowsShares", "editFollowsShares" -> "accessFollowsShares",
    "onlyEditorsShare" -> "accessFollowsShares", "onlyEditorsUnshare" -> "accessFollowsShares",
    "onlyEditorsMove" -> "accessFollowsShares", "onlyEditorsInvite" -> "invitationsAreOffers",
    "invitingGivesNoAccess" -> "invitationsAreOffers", "onlyTheInvitedAccept" -> "invitationsAreOffers",
    "onlyEditorsTrash" -> "trashUntilGone", "restoredOnlyBeforeGone" -> "trashUntilGone",
    "askingChangesNothingKept" -> "accessRequestsAreAsks", "onlyEditorsAnswer" -> "accessRequestsAreAsks",
    "approvedOnlyWhilePending" -> "accessRequestsAreAsks", "onlyTheOwnerHandsOn" -> "ownersKeepTheirDocuments",
    "newOwnerOwnsForGood" -> "ownersKeepTheirDocuments", "nobodyUnsharesAnOwner" -> "ownersKeepTheirDocuments",
    "nobodyReplacesAnOwner" -> "ownersKeepTheirDocuments", "viewingRestsOnTheLog" -> "auditTrail",
    "remindersOnTime" -> "requestsAnsweredOnTime", "endedSharesStayEnded" -> "endedStaysEnded",
    "lapsedInvitationsStayLapsed" -> "endedStaysEnded", "goneDocumentsStayGone" -> "endedStaysEnded",
    "housekeepingRunsCleanly" -> "housekeepingJob", "failedHousekeepingChangesNothing" -> "housekeepingJob",
    "housekeepingNotesItsRun" -> "housekeepingJob", "housekeepingSendsNoMail" -> "housekeepingJob",
    "failedDeliveryChangesNothing" -> "deliveryJob", "deliveryOnlyEmptiesTheOutbox" -> "deliveryJob",
    "deliveryTakesOutOnlyWhatWasSent" -> "deliveryJob", "deliveryTouchesOnlyWhatItSends" -> "deliveryJob",
    "jobsWiring" -> "serverWiring")

  /** The port's rules of the World, each split into one rule per fact. */
  private val rules: Map[String, String] = Map("sharesLogged" -> "logKept", "noticesLogged" -> "logKept",
    "trashNotGoneAtHousekeeping" -> "nothingEndedAtHousekeeping",
    "invitationsOpenAtHousekeeping" -> "nothingEndedAtHousekeeping",
    "requestsPendingAtHousekeeping" -> "nothingEndedAtHousekeeping",
    "remindedAtHousekeeping" -> "nothingEndedAtHousekeeping")

  private def split(parts: String) =
    s"split into smaller statements: $parts, one fact each, which together say what it said"
  private def contracts(cs: String) = s"$cs, each a part of the smaller statements that read it"

  /** Each difference the split makes, with why: the new parts, and the parents whose parts changed. */
  val differences: Map[String, (String, String)] =
    newParts.map((a, p) => a -> ("new" -> s"a part of $p: ${split(s"today's $p")}")) ++
      rules.map((r, p) => r -> ("new" -> ("a rule of the World (owner §45 D), kept by each program: one fact of the " +
        s"port's $p, ${split(s"its ${rules.count(_._2 == p)} facts")}"))) ++ Map(
      "accessFollowsShares" -> (("editPermission, whoMayEdit, viewFollowsShares, editFollowsShares, " +
        "onlyEditorsShare, onlyEditorsUnshare, onlyEditorsMove are parts; accessContract, canViewContract, " +
        "canEditContract, shareContract, unshareContract, moveContract no part") ->
        ("the purpose is stated over Declarations (owner §14, §27), one rule a line; " + split("its access lines " +
          "viewFollowsShares and editFollowsShares, and who shares, unshares and moves onlyEditorsShare, " +
          "onlyEditorsUnshare and onlyEditorsMove") + "; " + contracts("the contracts and the words' claims") +
          "; editPermission and whoMayEdit read its lines over may edit from the branches'")),
      "invitationsAreOffers" -> (("inTrash, onlyEditorsInvite, invitingGivesNoAccess, onlyTheInvitedAccept are " +
        "parts; " +
        "accessContract, inviteContract, acceptContract, withdrawContract no part") ->
        (split("onlyEditorsInvite, invitingGivesNoAccess, onlyTheInvitedAccept") + "; " +
          contracts("the contracts") + "; inTrash, as today's port has it, its step reading access over any word the " +
          "code calls; its line about the World is invitationsLapseOnTime's")),
      "trashUntilGone" -> (("onlyEditorsTrash, restoredOnlyBeforeGone are parts; trashContract, restoreContract " +
        "no part") ->
        (split("onlyEditorsTrash, restoredOnlyBeforeGone") + "; " + contracts("the contracts") +
          "; its line about the World is trashPurgedOnTime's")),
      "accessRequestsAreAsks" -> (("askingChangesNothingKept, onlyEditorsAnswer, approvedOnlyWhilePending, " +
        "remindersOnTime are parts; askContract, approveContract, declineContract no part") ->
        (split("askingChangesNothingKept, onlyEditorsAnswer, approvedOnlyWhilePending") + "; " +
          contracts("the contracts") + "; its two lines about the World are the two deadlines', today's " +
          "requestsAnsweredOnTime split into requestsAnsweredOnTime and remindersOnTime")),
      "ownersKeepTheirDocuments" -> (("ownersShare, onlyTheOwnerHandsOn, newOwnerOwnsForGood, nobodyUnsharesAnOwner, " +
        "nobodyReplacesAnOwner are parts; shareContract, unshareContract, transferContract no part") ->
        (split("onlyTheOwnerHandsOn, newOwnerOwnsForGood, nobodyUnsharesAnOwner, nobodyReplacesAnOwner") + "; " +
          contracts("the contracts") + "; ownersShare, what an owner's share is, moved from the purpose to it")),
      "auditTrail" -> ("viewingRestsOnTheLog is a part" -> (split("viewingRestsOnTheLog, and the rule sharesLogged " +
        "read at this moment") + "; permission is a part of that part")),
      "endedStaysEnded" -> (("endedSharesStayEnded, lapsedInvitationsStayLapsed, goneDocumentsStayGone are parts; " +
        "inForceContract, isOpenContract, goneContract no part") ->
        (split("endedSharesStayEnded, lapsedInvitationsStayLapsed, goneDocumentsStayGone") + "; " +
          contracts("the lifetimes' claims") + "; a root of its own: housekeepingClearsOnlyTheEnded restated it " +
          "as a line of its own, which no step needs")),
      "housekeepingClearsOnlyTheEnded" -> ("endedStaysEnded no part" -> ("its second line restated endedStaysEnded " +
        "(the restates warning): it says now only that housekeeping clears away only what has ended, through " +
        "clearsOnlyTheEnded, and endedStaysEnded is a root of its own")))

  /** Each new part, and each parent split, not stated against today's in `Port.lean`, with why. */
  val unstated: Map[String, String] =
    (newParts.keySet ++ rules.keySet).map(_ -> ("new: a smaller statement split from a node of today's or of the " +
      "port's, no " +
      "statement of today's to state it against alone")).toMap ++
      List("housekeepingClearsOnlyTheEnded", "ownersKeepTheirDocuments").map(_ -> ("split into smaller " +
        "statements: today's " +
        "statement is the conjunction of its parts', stated over the port's defines (`changes`, `mayHandOn`, " +
        "`ownsForGood`, `clearsOnlyTheEnded`); today's endedStaysEnded line is a root of its own")).toMap

  /** Where each new node stands: each claim proven (its own check), the new design with nothing to prove. */
  val standings: Map[String, List[String]] =
    (newParts.keySet - "jobsWiring" ++ rules.keySet).map(_.capitalize -> List("claim", "proven", "proven", "")).toMap +
      ("JobsWiring" -> List("design", "nothing to prove", "", ""))
