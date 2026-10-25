package sharing

import frflow.*
import sharing.domain.*
import sharing.housekeeping.Housekeeping
import sharing.http.{Request, SharingHttp}
import sharing.invitations.Invitations
import sharing.service.Sharing
import sharing.store.LibraryStore
import sharing.time.{ClockKept, Deadlines, Lifetimes, Run}
import sharing.trash.Trash

/** How the service is served, owned as a design decision. */
val serverWiring = Node.design("ServerWiring",
  "The server reads each HTTP request into a request (an unreadable one is answered 400 with its reason, an unknown route 404), answers it with HandleContract's flow on the store and the clock, one request or housekeeping run at a time, and writes the answer as JSON (a refused change is 403); requests run on a pool of workers with a time limit each (503 past it), and an internal error is answered 500 and logged. On the computer's clock, housekeeping runs every minute on a thread of its own, each start checked against HousekeepingOnTime; on a fake clock (tests), time moves and housekeeping runs only when a test asks.",
  why = "What a request is answered with, and what it leaves in the store, is proven (HandleContract); what a run of housekeeping leaves is proven too (HousekeepingJob). Reading HTTP, the routes, the threads, the schedule and the time limits are decided here and reviewed; the reading and writing of HTTP is tested against the routes this states (SharingSuite). One at a time makes each read the library the last one left, which both flows assume. The services' plain Scala objects run the same proven code.",
  idea = "Serving"
)("src/main/scala/sharing/http/Server.scala", "src/main/scala/sharing/http/HttpCodec.scala", "src/main/scala/sharing/http/Requests.scala",
  "src/main/scala/sharing/service/SharingService.scala", "src/main/scala/sharing/invitations/InvitationsService.scala",
  "src/main/scala/sharing/trash/TrashService.scala", "src/main/scala/sharing/housekeeping/HousekeepingService.scala",
  "src/main/scala/sharing/time/LifetimesService.scala").under(SharingHttp.handleContract)

/** The domain's types and the demo library, owned with the nodes they are the words of. */
val domainTypes = Node.design("DomainTypes",
  "People, teams, documents, folders, shares and invitations are plain data: a document and a folder each list the folders around them, outermost first; a team lists its people; a share may carry its end, a document the time it went to the trash, an invitation the time it was sent, all in seconds. The demo library (Demo.scala) is the data the examples are decided on.",
  why = "Listing the folders around a document, rather than only its parent, says what is inside a folder without walking the tree: every statement about folders is then a question about a list, with no depth to bound. A move keeps the lists right (MoveContract). Times are kept on the things they belong to, so what has ended is read off the data and the clock, never off a job having run. Owning these files makes a change to the types or to the example data a decision.",
  idea = "Who can see and change what"
)("src/main/scala/sharing/domain", "src/main/scala/sharing/Demo.scala").under(accessFollowsShares)

val knowledge = KnowledgeBase("Sharing", idea = "IDEA.md")(
  reach, cover, permission, trashed,
  accessFollowsShares,
  Sharing.accessContract, Sharing.canViewContract, Sharing.canEditContract,
  Sharing.shareContract, Sharing.unshareContract, Sharing.moveContract,
  Invitations.inviteContract, Invitations.acceptContract, Invitations.withdrawContract,
  Trash.trashContract, Trash.restoreContract,
  Housekeeping.tidyContract, Housekeeping.jobContract,
  Lifetimes.invitationLifetime, Lifetimes.trashLifetime, Run.housekeepingPeriod,
  Lifetimes.inForceContract, Lifetimes.isOpenContract, Lifetimes.goneContract,
  Deadlines.expiredSharesGiveNoAccess, Deadlines.invitationsAcceptedInTime, Deadlines.trashPurgedOnTime,
  Deadlines.invitationsLapseOnTime, Deadlines.endedStaysEnded,
  Run.clockNeverGoesBack, Run.housekeepingOnTime,
  LibraryStore.libraryKept, ClockKept.clockKept,
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
  .implementProven(Housekeeping.tidyContract)(Housekeeping.tidyCode)
  .implementProven(Housekeeping.jobContract)(() => Housekeeping.housekeeping)
  .implementProven(Lifetimes.inForceContract)(Lifetimes.inForceCode)
  .implementProven(Lifetimes.isOpenContract)(Lifetimes.isOpenCode)
  .implementProven(Lifetimes.goneContract)(Lifetimes.goneCode)
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
  .generating(vocabulary.libraries.describedAs("libraries over the vocabulary: q3 in reports or not, documents anywhere, in the trash or not, any shares and invitations"))
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
    yield
      val at = (places ++ List(None, None)).take(2).map(_.fold(Nil)(f => around(f) :+ f))
      val bin = (bins ++ List(None, None)).take(2)
      Library(
        List(Document(DocumentId("plan"), "Plan", at(0), bin(0)), Document(DocumentId("q3-report"), "Q3 report", at(1), bin(1))),
        List(Folder(reports, "Reports", Nil), Folder(q3, "Q3", around(q3))),
        List(Team(TeamId("eng"), eng.distinct), Team(TeamId("ops"), ops.distinct)),
        ss, is.take(3))

  val requests: Gen[Request] = Gen.choose(0, 8).flatMap {
    case 0 => for p <- people; d <- documents yield Request.Access(p, d)
    case 1 => for by <- people; t <- targets; g <- grantees; l <- levels; u <- maybe(times) yield Request.Share(by, t, g, l, u)
    case 2 => for by <- people; t <- targets; g <- grantees yield Request.Unshare(by, t, g)
    case 3 => for by <- people; d <- documents; into <- Gen.oneOf(None, Some(reports), Some(q3), Some(FolderId("nowhere"))) yield Request.Move(by, d, into)
    case 4 => for by <- people; to <- people; t <- targets; l <- levels yield Request.Invite(by, to, t, l)
    case 5 => for p <- people; t <- targets yield Request.Accept(p, t)
    case 6 => for by <- people; to <- people; t <- targets yield Request.Withdraw(by, to, t)
    case 7 => for by <- people; d <- documents yield Request.Trash(by, d)
    case _ => for by <- people; d <- documents yield Request.Restore(by, d)
  }

object sharingCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/sharing", extensions = List(frflow.agent.Agent))
