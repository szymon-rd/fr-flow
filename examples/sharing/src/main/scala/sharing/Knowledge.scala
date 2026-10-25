package sharing

import frflow.*
import sharing.audit.Audit
import sharing.domain.*
import sharing.housekeeping.Housekeeping
import sharing.http.SharingHttp
import sharing.invitations.Invitations
import sharing.notifications.Notifications
import sharing.ownership.Ownership
import sharing.requests.AccessRequests
import sharing.service.Sharing
import sharing.store.LibraryStore
import sharing.time.{ClockKept, Deadlines, Lifetimes, Run}
import sharing.trash.Trash

/** How the service is served, owned as a design decision. */
val serverWiring = Node.design("ServerWiring",
  "The server reads each HTTP request into a request (an unreadable one is answered 400 with its reason, an unknown route 404), answers it with HandleContract's flow on the store and the clock, in IO, as many at once as its workers take, and writes the answer as JSON (a refused change is 403); requests run on a pool of workers with a time limit each (503 past it), a request the store fails is answered 503 and changes nothing, and an internal error is answered 500 and logged. On the computer's clock, housekeeping runs every minute on a thread of its own, each start checked against HousekeepingOnTime, and delivery every ten seconds; a run that fails is tried again at its next start; on a fake clock (tests), time moves and housekeeping runs only when a test asks.",
  why = "What a request is answered with, and what it leaves in the store, is proven (HandleContract); what a run of housekeeping or of delivery leaves is proven too (HousekeepingJob, DeliveryJob). Reading HTTP, the routes, the threads, the schedule and the time limits are decided here and reviewed; the reading and writing of HTTP is tested against the routes this states (SharingSuite). Requests, housekeeping and delivery run at once (Q18-Q20); each reads the library the last transaction left (Transactions). The services' plain Scala objects run the same proven code.",
  idea = "Serving"
)("src/main/scala/sharing/http/Server.scala", "src/main/scala/sharing/http/HttpCodec.scala",
  "src/main/scala/sharing/service/SharingService.scala", "src/main/scala/sharing/invitations/InvitationsService.scala",
  "src/main/scala/sharing/trash/TrashService.scala", "src/main/scala/sharing/housekeeping/HousekeepingService.scala",
  "src/main/scala/sharing/time/LifetimesService.scala", "src/main/scala/sharing/requests/AccessRequestsService.scala",
  "src/main/scala/sharing/ownership/OwnershipService.scala").under(SharingHttp.handleContract)

/** The domain's types and the demo library, owned with the nodes they are the words of. */
val domainTypes = Node.design("DomainTypes",
  "People, teams, documents, folders, shares, invitations, access requests, log entries and notices are plain data: a document and a folder each list the folders around them, outermost first; a document names its owner; a team lists its people; a share may carry its end, a document the time it went to the trash, an invitation the time it was sent, a request the time it was made, all in seconds. The library keeps its log and its outbox with it. The demo library (Demo.scala) is the data the examples are decided on.",
  why = "Listing the folders around a document, rather than only its parent, says what is inside a folder without walking the tree: every statement about folders is then a question about a list, with no depth to bound. A move keeps the lists right (MoveContract). Times are kept on the things they belong to, so what has ended is read off the data and the clock, never off a job having run. Owning these files makes a change to the types or to the example data a decision.",
  idea = "Who can see and change what"
)("src/main/scala/sharing/domain", "src/main/scala/sharing/Demo.scala").under(accessFollowsShares)

val knowledge = KnowledgeBase("Sharing", idea = "IDEA.md")(
  reach, cover, permission, trashed, owner,
  accessFollowsShares, Invitations.invitationsAreOffers, Trash.trashUntilGone, Housekeeping.clearsOnlyTheEnded,
  AccessRequests.requestsAreAsks, Ownership.ownersKeepTheirDocuments, Audit.auditTrail, Notifications.noticesFollowChanges,
  Sharing.accessContract, Sharing.canViewContract, Sharing.canEditContract,
  Sharing.shareContract, Sharing.unshareContract, Sharing.moveContract,
  Invitations.inviteContract, Invitations.acceptContract, Invitations.withdrawContract,
  Trash.trashContract, Trash.restoreContract,
  AccessRequests.askContract, AccessRequests.approveContract, AccessRequests.declineContract, AccessRequests.chaseContract,
  Ownership.transferContract, Audit.recordContract, Audit.forgetContract, Notifications.announceContract, Notifications.warnContract,
  Housekeeping.tidyContract, Housekeeping.jobContract, Notifications.deliveryJob,
  Lifetimes.invitationLifetime, Lifetimes.trashLifetime, Lifetimes.requestLifetime, Run.housekeepingPeriod,
  Lifetimes.inForceContract, Lifetimes.isOpenContract, Lifetimes.goneContract, Lifetimes.isPendingContract, Lifetimes.reminderDueContract,
  Deadlines.trashPurgedOnTime,
  Deadlines.invitationsLapseOnTime, Deadlines.requestsAnsweredOnTime, Deadlines.endedStaysEnded,
  Run.clockNeverGoesBack, Run.housekeepingOnTime,
  LibraryStore.libraryKept, LibraryStore.transactions, Notifications.mailerKept, ClockKept.clockKept,
  SharingHttp.handleContract,
  serverWiring, domainTypes)
  .implementProven(Sharing.accessContract)(Sharing.accessCode)
  .implementProven(Sharing.canViewContract)(Sharing.canViewCode)
  .implementProven(Sharing.canEditContract)(Sharing.canEditCode)
  .implementProven(Sharing.shareContract)(Sharing.shareCode)
  .implementProven(Sharing.unshareContract)(Sharing.unshareCode)
  .implementProven(Sharing.moveContract)(Sharing.moveCode)
  .implementProven(Invitations.inviteContract)(Invitations.inviteCode)
  .implementProven(Invitations.acceptContract)(Invitations.acceptCode)
  .implementProven(Invitations.withdrawContract)(Invitations.withdrawCode)
  .implementProven(Trash.trashContract)(Trash.trashCode)
  .implementProven(Trash.restoreContract)(Trash.restoreCode)
  .implementProven(AccessRequests.askContract)(AccessRequests.askCode)
  .implementProven(AccessRequests.approveContract)(AccessRequests.approveCode)
  .implementProven(AccessRequests.declineContract)(AccessRequests.declineCode)
  .implementProven(AccessRequests.chaseContract)(AccessRequests.chaseCode)
  .implementProven(Ownership.transferContract)(Ownership.transferCode)
  .implementProven(Audit.recordContract)(Audit.recordCode)
  .implementProven(Notifications.announceContract)(Notifications.announceCode)
  .implementProven(Audit.forgetContract)(Audit.forgetCode)
  .implementProven(Notifications.warnContract)(Notifications.warnCode)
  .implementProven(Notifications.deliveryJob)(() => Notifications.delivery)
  .implementProven(Housekeeping.tidyContract)(Housekeeping.tidyCode)
  .implementProven(Housekeeping.jobContract)(() => Housekeeping.housekeeping)
  .implementProven(Lifetimes.inForceContract)(Lifetimes.inForceCode)
  .implementProven(Lifetimes.isOpenContract)(Lifetimes.isOpenCode)
  .implementProven(Lifetimes.goneContract)(Lifetimes.goneCode)
  .implementProven(Lifetimes.isPendingContract)(Lifetimes.isPendingCode)
  .implementProven(Lifetimes.reminderDueContract)(Lifetimes.reminderDueCode)
  .implementProven(SharingHttp.handleContract)(SharingHttp.handleRequest)
  // Names from a small vocabulary, so generated shares meet the generated people, teams, documents and folders; times
  // near the demo's moment, so what is generated ends, lapses and goes within the times generated.
  .generating(vocabulary.people.describedAs("ann, bob, cat"))
  .generating(vocabulary.teams.describedAs("eng, ops"))
  .generating(vocabulary.documents.describedAs("plan, q3-report"))
  .generating(vocabulary.folders.describedAs("reports, q3"))
  .generating(vocabulary.times.describedAs("seconds within 40 days of the demo's moment, by hours and days"))
  .generating(vocabulary.targets.describedAs("the vocabulary's documents and folders"))
  .generating(vocabulary.grantees.describedAs("the vocabulary's people and teams"))
  .generating(vocabulary.shares.describedAs("shares over the vocabulary, for good or until a time"))
  .generating(vocabulary.invitations.describedAs("invitations over the vocabulary, sent at a time"))
  .generating(vocabulary.accessRequests.describedAs("access requests over the vocabulary, made at a time, reminded or not"))
  .generating(vocabulary.libraries.describedAs("libraries over the vocabulary: q3 in reports or not, documents anywhere, in the trash or not, owned by anyone, any shares, invitations and requests, a short log and outbox"))
  .generating(vocabulary.requests.describedAs("requests over the vocabulary: questions and every kind of change"))

/** The names and times generated data is drawn from. */
object vocabulary:
  val people: Gen[PersonId] = Gen.oneOf(PersonId("ann"), PersonId("bob"), PersonId("cat"))
  val teams: Gen[TeamId] = Gen.oneOf(TeamId("eng"), TeamId("ops"))
  val documents: Gen[DocumentId] = Gen.oneOf(DocumentId("plan"), DocumentId("q3-report"))
  val folders: Gen[FolderId] = Gen.oneOf(FolderId("reports"), FolderId("q3"))
  val times: Gen[BigInt] = for d <- Gen.choose(-40, 40); h <- Gen.choose(0, 23) yield Demo.now + d * Demo.day + h * 3600
  val targets: Gen[Target] = Gen.choose(0, 1).flatMap(i => if i == 0 then documents.map(Target.Doc(_)) else folders.map(Target.InFolder(_)))
  val grantees: Gen[Grantee] = Gen.choose(0, 1).flatMap(i => if i == 0 then people.map(Grantee.Person(_)) else teams.map(Grantee.Team(_)))
  private val levels: Gen[Level] = Gen.oneOf(Level.View, Level.Edit)
  private def maybe[A](g: Gen[A]): Gen[Option[A]] = Gen.choose(0, 1).flatMap(i => if i == 0 then Gen.const(None) else g.map(Some(_)))
  val shares: Gen[Share] = for t <- targets; g <- grantees; l <- levels; u <- maybe(times) yield Share(t, g, l, u)
  val invitations: Gen[Invitation] = for to <- people; t <- targets; l <- levels; by <- people; s <- times yield Invitation(to, t, l, by, s)
  val accessRequests: Gen[AccessRequest] =
    for p <- people; w <- targets; l <- levels; at <- times; r <- Gen.oneOf(true, false) yield AccessRequest(p, w, l, at, r)
  private val (reports, q3) = (FolderId("reports"), FolderId("q3"))

  /** Two folders, q3 inside reports or beside it; each document in no folder or in one of them, in the trash or not;
    * teams of any of the people; any shares and invitations.
    */
  val libraries: Gen[Library] =
    for
      nested  <- Gen.oneOf(true, false)
      around   = Map(reports -> Nil, q3 -> (if nested then List(reports) else Nil))
      places  <- Gen.listOf(Gen.oneOf(None, Some(reports), Some(q3)))
      bins    <- Gen.listOf(maybe(times))
      eng     <- Gen.listOf(people)
      ops     <- Gen.listOf(people)
      ss      <- Gen.listOf(shares)
      is      <- Gen.listOf(invitations)
      owners  <- Gen.listOf(people)
      rs      <- Gen.listOf(accessRequests)
      asked   <- Gen.listOf(requests)
      when    <- times
    yield
      val at = (places ++ List(None, None)).take(2).map(_.fold(Nil)(f => around(f) :+ f))
      val bin = (bins ++ List(None, None)).take(2)
      val own = (owners ++ List(PersonId("ann"), PersonId("ann"))).take(2)
      val log = asked.take(2).zipWithIndex.map((r, i) => Entry(i, when, Change.Made(r)))
      Library(
        List(Document(DocumentId("plan"), "Plan", at(0), bin(0), own(0)), Document(DocumentId("q3-report"), "Q3 report", at(1), bin(1), own(1))),
        List(Folder(reports, "Reports", Nil), Folder(q3, "Q3", around(q3))),
        List(Team(TeamId("eng"), eng.distinct), Team(TeamId("ops"), ops.distinct)),
        ss, is.take(3), rs.take(2), log, log.take(1).map(e => Notice(PersonId("cat"), Subject.Logged(e))))

  lazy val requests: Gen[Request] = Gen.choose(0, 12).flatMap {
    case 0 => for p <- people; d <- documents yield Request.Access(p, d)
    case 1 => for by <- people; t <- targets; g <- grantees; l <- levels; u <- maybe(times) yield Request.Share(by, t, g, l, u)
    case 2 => for by <- people; t <- targets; g <- grantees yield Request.Unshare(by, t, g)
    case 3 => for by <- people; d <- documents; into <- Gen.oneOf(None, Some(reports), Some(q3), Some(FolderId("nowhere"))) yield Request.Move(by, d, into)
    case 4 => for by <- people; to <- people; t <- targets; l <- levels yield Request.Invite(by, to, t, l)
    case 5 => for p <- people; t <- targets yield Request.Accept(p, t)
    case 6 => for by <- people; to <- people; t <- targets yield Request.Withdraw(by, to, t)
    case 7 => for by <- people; d <- documents yield Request.Trash(by, d)
    case 8 => for by <- people; d <- documents yield Request.Restore(by, d)
    case 9 => for p <- people; w <- targets; l <- levels yield Request.Ask(p, w, l)
    case 10 => for by <- people; p <- people; w <- targets yield Request.Approve(by, p, w)
    case 11 => for by <- people; p <- people; w <- targets yield Request.Decline(by, p, w)
    case _ => for by <- people; d <- documents; to <- people yield Request.Transfer(by, d, to)
  }

object sharingCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/sharing", extensions = List(frflow.agent.Agent))
