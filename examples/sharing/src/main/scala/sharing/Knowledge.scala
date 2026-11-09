package sharing

import cats.effect.IO
import frflow.*
import sharing.features.AccessRequests
import sharing.features.AccessRequestsClaims
import sharing.features.Audit
import sharing.features.AuditClaims
import sharing.features.Housekeeping
import sharing.features.HousekeepingClaims
import sharing.features.Invitations
import sharing.features.InvitationsClaims
import sharing.features.Ownership
import sharing.features.OwnershipClaims
import sharing.features.Sharing
import sharing.features.SharingClaims
import sharing.features.SharingHttp
import sharing.features.Trash
import sharing.features.TrashClaims
import sharing.notifications.{Mailer, MemoryMailer, MemoryPool, Pool}
import sharing.notifications.Notifications
import sharing.notifications.NotificationsClaims
import sharing.store.{LibraryStore, MemoryLibraryStore, Transactions}
import sharing.time.{ClockKept, Deadlines, Housekept, Lifetimes, Run}
import sharing.time.LifetimesClaims

val serverWiring = Node.design("The server answers each HTTP request, read into a request, with handleContract's " +
    "program on the store and the clock, as JSON, on a pool of workers that gives each request a time limit.")(
  "src/main/scala/sharing/http/Server.scala", "src/main/scala/sharing/http/HttpCodec.scala",
  "src/main/scala/sharing/service/SharingService.scala", "src/main/scala/sharing/invitations/InvitationsService.scala",
  "src/main/scala/sharing/trash/TrashService.scala", "src/main/scala/sharing/time/LifetimesService.scala",
  "src/main/scala/sharing/requests/AccessRequestsService.scala",
  "src/main/scala/sharing/ownership/OwnershipService.scala").refines(SharingHttp.handleContract)

val jobsWiring = Node.design("On the computer's clock, housekeeping is started every minute and delivery every ten " +
    "seconds, so a run that fails is tried again at its next start.")(
  "src/main/scala/sharing/housekeeping/HousekeepingService.scala")
  .refines(HousekeepingClaims.housekeepingRunsCleanly, NotificationsClaims.deliveryJob)

val domainTypes = Node.design("The domain's records (people, teams, documents, folders, shares, invitations, access " +
    "requests, log entries and notices) are plain data, kept together in one library with its log and its outbox.")(
  "src/main/scala/sharing/domain", "src/main/scala/sharing/Demo.scala").refines(accessFollowsShares)

/** Sharing's nodes: the words, the purpose and its parts, the branches with theirs, the contracts, the deadlines and
  * the World's rules, the assumptions, the designs.
  */
val nodes: List[Node] = List(
  reach, cover, permission, editPermission, Definitions.inTrash, ownersShare, whoMayEdit, whatIsTrashed,
  accessFollowsShares, viewFollowsShares, editFollowsShares, onlyEditorsShare, onlyEditorsUnshare, onlyEditorsMove,
  sharing.invitationsAreOffers, sharing.onlyEditorsInvite, sharing.invitingGivesNoAccess, sharing.onlyTheInvitedAccept,
  sharing.trashUntilGone, sharing.onlyEditorsTrash, sharing.restoredOnlyBeforeGone,
  sharing.accessRequestsAreAsks, sharing.askingChangesNothingKept, sharing.onlyEditorsAnswer,
  sharing.approvedOnlyWhilePending, sharing.ownersKeepTheirDocuments, sharing.onlyTheOwnerHandsOn,
  sharing.newOwnerOwnsForGood, sharing.nobodyUnsharesAnOwner, sharing.nobodyReplacesAnOwner,
  sharing.housekeepingClearsOnlyTheEnded, sharing.auditTrail, sharing.viewingRestsOnTheLog,
  sharing.noticesFollowChanges,
  SharingClaims.accessContract, SharingClaims.canViewContract, SharingClaims.canEditContract,
  SharingClaims.shareContract, SharingClaims.unshareContract, SharingClaims.moveContract,
  InvitationsClaims.inviteContract, InvitationsClaims.acceptContract, InvitationsClaims.withdrawContract,
  TrashClaims.trashContract, TrashClaims.restoreContract, AccessRequestsClaims.askContract,
  AccessRequestsClaims.approveContract, AccessRequestsClaims.declineContract, AccessRequestsClaims.chaseContract,
  OwnershipClaims.transferContract, AuditClaims.recordContract, AuditClaims.forgetContract,
  NotificationsClaims.announceContract, NotificationsClaims.warnContract, HousekeepingClaims.tidyContract,
  HousekeepingClaims.housekeepingJob, HousekeepingClaims.housekeepingRunsCleanly,
  HousekeepingClaims.failedHousekeepingChangesNothing, HousekeepingClaims.housekeepingNotesItsRun,
  HousekeepingClaims.housekeepingSendsNoMail, NotificationsClaims.deliveryJob,
  NotificationsClaims.failedDeliveryChangesNothing, NotificationsClaims.deliveryOnlyEmptiesTheOutbox,
  NotificationsClaims.deliveryTakesOutOnlyWhatWasSent, NotificationsClaims.deliveryTouchesOnlyWhatItSends,
  NotificationsClaims.deliveryGivesBack,
  LifetimesClaims.invitationLifetime, LifetimesClaims.trashLifetime, LifetimesClaims.requestLifetime,
  LifetimesClaims.reminderTime,
  Run.housekeepingPeriod, LifetimesClaims.inForceContract, LifetimesClaims.isOpenContract,
  LifetimesClaims.goneContract, LifetimesClaims.pendingContract, LifetimesClaims.reminderDueContract,
  Deadlines.trashPurgedOnTime, Deadlines.invitationsLapseOnTime, Deadlines.requestsAnsweredOnTime,
  Deadlines.remindersOnTime, Deadlines.endedStaysEnded, Deadlines.endedSharesStayEnded,
  Deadlines.lapsedInvitationsStayLapsed, Deadlines.goneDocumentsStayGone, Deadlines.timeMovesOn,
  Deadlines.housekeptLately, Deadlines.trashNotGoneAtHousekeeping, Deadlines.invitationsOpenAtHousekeeping,
  Deadlines.requestsPendingAtHousekeeping, Deadlines.remindedAtHousekeeping,
  sharing.sharesLogged, sharing.noticesLogged, ClockKept.housekeepingOnTime, ClockKept.clockStarts,
  ClockKept.housekeptStarts, ClockKept.housekeptKept, ClockKept.housekeptOneAtATime, LibraryStore.libraryKept,
  LibraryStore.libraryStarts, LibraryStore.oneTransactionAtATime, Transactions.transactions, Notifications.mailerKept,
  Notifications.mailOneAtATime, Pool.poolKept, Pool.poolOneAtATime,
  SharingHttp.handleContract, serverWiring, jobsWiring, domainTypes)

/** Sharing: its nodes, and the code of every Definition. */
val knowledge: FrModel = withCode(FrModel("Sharing")(nodes*)).implementProven(Sharing.access)(Sharing.accessCode)

/** `kb` with the code of every Definition of sharing but `access`: the proven code of the words, the operations and
  * the programs, the fixed lifetimes, when the service started, and each model's Scala.
  */
def withCode(kb: FrModel): FrModel = models(lifetimes(programs(operations(words(kb)))))

/** The purpose's words' proven code. */
private def words(kb: FrModel): FrModel = kb
  .implementProven(reaches)(reachesCode)
  .implementProven(covers)(coversCode)
  .implementProven(mayEdit)(mayEditCode)
  .implementProven(inTrash)(inTrashCode)
  .implementProven(ownedBy)(ownedByCode)

/** The operations' proven code, but access's. */
private def operations(kb: FrModel): FrModel = kb
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

/** The three programs' proven code, and tidying's. */
private def programs(kb: FrModel): FrModel = kb
  .implementProven(Notifications.deliver)(Notifications.delivery)
  .implementProven(Housekeeping.tidy)(Housekeeping.tidyCode)
  .implementProven(Housekeeping.housekeep)(Housekeeping.housekeeping)
  .implementProven(SharingHttp.handle)(SharingHttp.handleRequest)

/** The lifetimes' proven code, and their fixed durations. */
private def lifetimes(kb: FrModel): FrModel = kb
  .implementProven(Lifetimes.inForce)(Lifetimes.inForceCode)
  .implementProven(Lifetimes.isOpen)(Lifetimes.isOpenCode)
  .implementProven(Lifetimes.gone)(Lifetimes.goneCode)
  .implementProven(Lifetimes.isPending)(Lifetimes.isPendingCode)
  .implementProven(Lifetimes.reminderDue)(Lifetimes.reminderDueCode)
  .implementValue(Lifetimes.invitationLasts)(BigInt(7 * 86400))
  .implementValue(Lifetimes.trashKeeps)(BigInt(30 * 86400))
  .implementValue(Lifetimes.requestLasts)(BigInt(7 * 86400))
  .implementValue(Lifetimes.remindAfter)(BigInt(2 * 86400))
  .implementValue(Run.housekeepingWithin)(BigInt(120))

/** When the service started, provided; each model's Scala. */
private def models(kb: FrModel): FrModel = kb
  .implementProvided(Run.startedAt)
  .implementTested(ClockKept.ranAt)(start = Housekept.at, observe = _.last)(h => Tuple1(h.ranAt))
  .implementTested(LibraryStore.load, LibraryStore.save)(start = MemoryLibraryStore.holding, observe = _.library)(
    s => (s.load, s.save))
  .implementTested(Mailer.send)(start = MemoryMailer.holding, observe = _.boxes)(m => Tuple1(m.send))
  .implementTested(Clock.now, Clock.sleep, Clock.elapse)(start = Wall.at[IO], observe = _.time)(c =>
      (c.now, c.sleep, c.elapse))
  .implementTested(Pool.take, Pool.give)(start = MemoryPool.holding, observe = _.count)(p => (p.take, p.give))
