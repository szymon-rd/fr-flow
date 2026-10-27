package sharing

import frflow.*
import sharing.audit.Audit
import sharing.housekeeping.Housekeeping
import sharing.http.SharingHttp
import sharing.invitations.Invitations
import sharing.notifications.Notifications
import sharing.ownership.Ownership
import sharing.requests.AccessRequests
import sharing.service.Sharing
import sharing.store.{LibraryStore, Transactions}
import sharing.time.{ClockKept, Deadlines, Lifetimes, Run}
import sharing.trash.Trash

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
  reach, cover, permission, Definitions.inTrash, ownersShare,
  accessFollowsShares, Invitations.invitationsAreOffers, Trash.trashUntilGone,
  Housekeeping.housekeepingClearsOnlyTheEnded, AccessRequests.accessRequestsAreAsks,
  Ownership.ownersKeepTheirDocuments, Audit.auditTrail, Notifications.noticesFollowChanges,
  Sharing.accessContract, Sharing.canViewContract, Sharing.canEditContract,
  Sharing.shareContract, Sharing.unshareContract, Sharing.moveContract,
  Invitations.inviteContract, Invitations.acceptContract, Invitations.withdrawContract,
  Trash.trashContract, Trash.restoreContract,
  AccessRequests.askContract, AccessRequests.approveContract, AccessRequests.declineContract,
  AccessRequests.chaseContract, Ownership.transferContract, Audit.recordContract, Audit.forgetContract,
  Notifications.announceContract, Notifications.warnContract,
  Housekeeping.tidyContract, Housekeeping.housekeepingJob, Notifications.deliveryJob,
  Lifetimes.invitationLifetime, Lifetimes.trashLifetime, Lifetimes.requestLifetime, Run.housekeepingPeriod,
  Lifetimes.inForceContract, Lifetimes.isOpenContract, Lifetimes.goneContract, Lifetimes.pendingContract,
  Lifetimes.reminderDueContract, Deadlines.trashPurgedOnTime, Deadlines.invitationsLapseOnTime,
  Deadlines.requestsAnsweredOnTime, Deadlines.endedStaysEnded, Run.clockNeverGoesBack, Run.housekeepingOnTime,
  LibraryStore.libraryKept, LibraryStore.oneTransactionAtATime, Transactions.transactions, Notifications.mailerKept,
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
