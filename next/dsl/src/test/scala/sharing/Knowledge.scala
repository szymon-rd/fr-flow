package sharing

import frflow.*
import sharing.audit.Audit
import sharing.audit.AuditClaims
import sharing.housekeeping.Housekeeping
import sharing.housekeeping.HousekeepingClaims
import sharing.http.SharingHttp
import sharing.invitations.Invitations
import sharing.invitations.InvitationsClaims
import sharing.notifications.Notifications
import sharing.notifications.NotificationsClaims
import sharing.ownership.Ownership
import sharing.ownership.OwnershipClaims
import sharing.requests.AccessRequests
import sharing.requests.AccessRequestsClaims
import sharing.service.Sharing
import sharing.service.SharingClaims
import sharing.store.{LibraryStore, Transactions}
import sharing.time.LifetimesClaims
import sharing.time.{ClockKept, Deadlines, Lifetimes, Run}
import sharing.trash.Trash
import sharing.trash.TrashClaims

val serverWiring = Node.design("The server reads each HTTP request into a request, answers it with handleContract's " +
    "program on the store and the clock, in IO, as many at once as its workers take, and writes the answer as JSON; " +
    "requests run on a pool of workers with a time limit each, a request the store fails is answered 503 and changes " +
    "nothing. On the computer's clock, housekeeping runs every minute and delivery every ten seconds; a run that " +
    "fails is tried again at its next start.")(
  "src/main/scala/sharing/http/Server.scala", "src/main/scala/sharing/http/HttpCodec.scala",
  "src/main/scala/sharing/service/SharingService.scala", "src/main/scala/sharing/invitations/InvitationsService.scala",
  "src/main/scala/sharing/trash/TrashService.scala", "src/main/scala/sharing/housekeeping/HousekeepingService.scala",
  "src/main/scala/sharing/time/LifetimesService.scala", "src/main/scala/sharing/requests/AccessRequestsService.scala",
  "src/main/scala/sharing/ownership/OwnershipService.scala").refines(SharingHttp.handleContract)

val domainTypes = Node.design("People, teams, documents, folders, shares, invitations, access requests, log entries " +
    "and notices are plain data: a document and a folder each list the folders around them, outermost first; a " +
    "document names its owner; a team lists its people; a share may carry its end, a document the time it went to " +
    "the trash, an invitation the time it was sent, a request the time it was made, all in seconds. The library " +
    "keeps its log and its outbox with it.")(
  "src/main/scala/sharing/domain", "src/main/scala/sharing/Demo.scala").refines(accessFollowsShares)

val knowledge = KnowledgeBase("Sharing")(
  reach, cover, Definitions.mayView, Definitions.mayEdit, Definitions.inTrash, ownersShare, accessFollowsShares,
  sharing.invitationsAreOffers, sharing.trashUntilGone, sharing.housekeepingClearsOnlyTheEnded,
  sharing.accessRequestsAreAsks, sharing.ownersKeepTheirDocuments, sharing.auditTrail, sharing.noticesFollowChanges,
  SharingClaims.accessContract, SharingClaims.canViewContract, SharingClaims.canEditContract,
  SharingClaims.shareContract, SharingClaims.unshareContract, SharingClaims.moveContract,
  InvitationsClaims.inviteContract, InvitationsClaims.acceptContract, InvitationsClaims.withdrawContract,
  TrashClaims.trashContract, TrashClaims.restoreContract, AccessRequestsClaims.askContract,
  AccessRequestsClaims.approveContract, AccessRequestsClaims.declineContract, AccessRequestsClaims.chaseContract,
  OwnershipClaims.transferContract, AuditClaims.recordContract, AuditClaims.forgetContract,
  NotificationsClaims.announceContract, NotificationsClaims.warnContract, HousekeepingClaims.tidyContract,
  HousekeepingClaims.housekeepingJob, NotificationsClaims.deliveryJob, LifetimesClaims.invitationLifetime,
  LifetimesClaims.trashLifetime, LifetimesClaims.Lengths.requestLasts, LifetimesClaims.Lengths.remindAfter,
  Run.housekeepingPeriod, LifetimesClaims.inForceContract, LifetimesClaims.isOpenContract,
  LifetimesClaims.goneContract, LifetimesClaims.pendingContract, LifetimesClaims.reminderDueContract,
  Deadlines.trashPurgedOnTime, Deadlines.invitationsLapseOnTime, Deadlines.requestsAnsweredOnTime,
  Deadlines.endedStaysEnded, Run.clockNeverGoesBack, Run.housekeepingOnTime, LibraryStore.libraryKept,
  LibraryStore.oneTransactionAtATime, Transactions.transactions, Notifications.mailerKept,
  Notifications.mailOneAtATime, ClockKept.clockKept, ClockKept.clockAlone, SharingHttp.handleContract, serverWiring,
  domainTypes)
  .implementProven(reaches)(reachesCode)
  .implementProven(covers)(coversCode)
  .implementProven(mayView)(mayViewCode)
  .implementProven(mayEdit)(mayEditCode)
  .implementProven(inTrash)(inTrashCode)
  .implementProven(ownedBy)(ownedByCode)
  .implementProven(Sharing.access)(Sharing.accessCode)
  .implementProven(Sharing.canView)(Sharing.canViewCode)
  .implementProven(Sharing.canEdit)(Sharing.canEditCode)
  .implementProven(Sharing.share)(Sharing.shareCode)
  .implementProven(Sharing.unshare)(Sharing.unshareCode)
  .implementProven(Sharing.move)(Sharing.moveCode)
  .implementProven(Invitations.invite)(Invitations.inviteCode)
  .implementProven(Invitations.accept)(Invitations.acceptCode)
  .implementProven(Invitations.withdraw)(Invitations.withdrawCode)
  .implementProven(Trash.trash)(Trash.trashCode)
  .implementProven(Trash.restore)(Trash.restoreCode)
  .implementProven(AccessRequests.ask)(AccessRequests.askCode)
  .implementProven(AccessRequests.approve)(AccessRequests.approveCode)
  .implementProven(AccessRequests.decline)(AccessRequests.declineCode)
  .implementProven(AccessRequests.chase)(AccessRequests.chaseCode)
  .implementProven(Ownership.transfer)(Ownership.transferCode)
  .implementProven(Audit.record)(Audit.recordCode)
  .implementProven(Audit.forget)(Audit.forgetCode)
  .implementProven(Notifications.announce)(Notifications.announceCode)
  .implementProven(Notifications.warn)(Notifications.warnCode)
  .implementProven(Notifications.deliver)(Notifications.delivery)
  .implementProven(Housekeeping.tidy)(Housekeeping.tidyCode)
  .implementProven(Housekeeping.housekeep)(Housekeeping.housekeeping)
  .implementProven(Lifetimes.inForce)(Lifetimes.inForceCode)
  .implementProven(Lifetimes.isOpen)(Lifetimes.isOpenCode)
  .implementProven(Lifetimes.gone)(Lifetimes.goneCode)
  .implementProven(Lifetimes.isPending)(Lifetimes.isPendingCode)
  .implementProven(Lifetimes.reminderDue)(Lifetimes.reminderDueCode)
  .implementProven(SharingHttp.handle)(SharingHttp.handleRequest)
  .implementValue(Lifetimes.invitationLasts)(BigInt(7 * 86400))
  .implementValue(Lifetimes.trashKeeps)(BigInt(30 * 86400))
  .implementValue(Lifetimes.requestLasts)(BigInt(7 * 86400))
  .implementValue(Lifetimes.remindAfter)(BigInt(2 * 86400))
  .implementValue(Run.housekeepingWithin)(BigInt(120))
  .implementProvided(Run.startedAt, Run.events)
