package sharing

import frflow.*
import sharing.domain.*
import sharing.http.{Request, SharingHttp}
import sharing.service.Sharing
import sharing.store.LibraryStore

/** How the service is served, owned as a design decision. */
val serverWiring = Node.design("ServerWiring",
  "The server reads each HTTP request into a request (an unreadable one is answered 400 with its reason, an unknown route 404), answers it with HandleContract's flow on the store, one request at a time, and writes the answer as JSON (a refused change is 403); requests run on a pool of workers with a time limit each (503 past it), and an internal error is answered 500 and logged.",
  why = "What a request is answered with, and what it leaves in the store, is proven (HandleContract). Reading HTTP, the routes, the threads and the time limits are decided here and reviewed; the reading and writing of HTTP is tested against the routes this states (SharingSuite). One request at a time makes each read the library the last one left, which HandleContract assumes. SharingService, Sharing's methods as plain Scala, runs the same proven code.",
  idea = "Who can see and change what"
)("src/main/scala/sharing/http/Server.scala", "src/main/scala/sharing/http/HttpCodec.scala", "src/main/scala/sharing/http/Requests.scala",
  "src/main/scala/sharing/service/SharingService.scala").under(SharingHttp.handleContract)

/** The domain's types and the demo library, owned with the nodes they are the words of. */
val domainTypes = Node.design("DomainTypes",
  "People, teams, documents, folders and shares are plain data: a document and a folder each list the folders around them, outermost first; a team lists its people. The demo library (Demo.scala) is the data the examples are decided on.",
  why = "Listing the folders around a document, rather than only its parent, says what is inside a folder without walking the tree: every statement about folders is then a question about a list, with no depth to bound. A move keeps the lists right (MoveContract). Owning these files makes a change to the types or to the example data a decision.",
  idea = "Who can see and change what"
)("src/main/scala/sharing/domain", "src/main/scala/sharing/Demo.scala").under(accessFollowsShares)

val knowledge = KnowledgeBase("Sharing", idea = "IDEA.md")(
  reach, cover, permission,
  accessFollowsShares,
  Sharing.accessContract, Sharing.canViewContract, Sharing.canEditContract,
  Sharing.shareContract, Sharing.unshareContract, Sharing.moveContract,
  LibraryStore.libraryKept,
  SharingHttp.handleContract,
  serverWiring, domainTypes)
  .implementProven(Sharing.accessContract)(Sharing.accessCode)
  .implementProven(Sharing.canViewContract)(Sharing.canViewCode)
  .implementProven(Sharing.canEditContract)(Sharing.canEditCode)
  .implementProven(Sharing.shareContract)(Sharing.shareCode)
  .implementProven(Sharing.unshareContract)(Sharing.unshareCode)
  .implementProven(Sharing.moveContract)(Sharing.moveCode)
  .implementProven(SharingHttp.handleContract)(SharingHttp.handleRequest)
  // Names from a small vocabulary, so generated shares meet the generated people, teams, documents and folders.
  .generating(vocabulary.people.describedAs("ann, bob, cat"))
  .generating(vocabulary.teams.describedAs("eng, ops"))
  .generating(vocabulary.documents.describedAs("plan, q3-report"))
  .generating(vocabulary.folders.describedAs("reports, q3"))
  .generating(vocabulary.targets.describedAs("the vocabulary's documents and folders"))
  .generating(vocabulary.grantees.describedAs("the vocabulary's people and teams"))
  .generating(vocabulary.libraries.describedAs("libraries over the vocabulary: q3 in reports or not, documents anywhere, any shares"))
  .generating(vocabulary.requests.describedAs("requests over the vocabulary: questions, shares, unshares and moves"))

/** The names generated data is drawn from. */
object vocabulary:
  val people: Gen[PersonId] = Gen.oneOf(PersonId("ann"), PersonId("bob"), PersonId("cat"))
  val teams: Gen[TeamId] = Gen.oneOf(TeamId("eng"), TeamId("ops"))
  val documents: Gen[DocumentId] = Gen.oneOf(DocumentId("plan"), DocumentId("q3-report"))
  val folders: Gen[FolderId] = Gen.oneOf(FolderId("reports"), FolderId("q3"))
  val targets: Gen[Target] = Gen.choose(0, 1).flatMap(i => if i == 0 then documents.map(Target.Doc(_)) else folders.map(Target.InFolder(_)))
  val grantees: Gen[Grantee] = Gen.choose(0, 1).flatMap(i => if i == 0 then people.map(Grantee.Person(_)) else teams.map(Grantee.Team(_)))
  private val levels: Gen[Level] = Gen.oneOf(Level.View, Level.Edit)
  private val shares: Gen[Share] = for t <- targets; g <- grantees; l <- levels yield Share(t, g, l)
  private val (reports, q3) = (FolderId("reports"), FolderId("q3"))

  /** Two folders, q3 inside reports or beside it; each document in no folder or in one of them; teams of any of the
    * people; any shares.
    */
  val libraries: Gen[Library] =
    for
      nested  <- Gen.oneOf(true, false)
      around   = Map(reports -> Nil, q3 -> (if nested then List(reports) else Nil))
      places  <- Gen.listOf(Gen.oneOf(None, Some(reports), Some(q3)))
      eng     <- Gen.listOf(people)
      ops     <- Gen.listOf(people)
      ss      <- Gen.listOf(shares)
    yield
      val at = (places ++ List(None, None)).take(2).map(_.fold(Nil)(f => around(f) :+ f))
      Library(
        List(Document(DocumentId("plan"), "Plan", at(0)), Document(DocumentId("q3-report"), "Q3 report", at(1))),
        List(Folder(reports, "Reports", Nil), Folder(q3, "Q3", around(q3))),
        List(Team(TeamId("eng"), eng.distinct), Team(TeamId("ops"), ops.distinct)),
        ss)

  val requests: Gen[Request] = Gen.choose(0, 3).flatMap {
    case 0 => for p <- people; d <- documents yield Request.Access(p, d)
    case 1 => for by <- people; t <- targets; g <- grantees; l <- levels yield Request.Share(by, t, g, l)
    case 2 => for by <- people; t <- targets; g <- grantees yield Request.Unshare(by, t, g)
    case _ => for by <- people; d <- documents; into <- Gen.oneOf(None, Some(reports), Some(q3), Some(FolderId("nowhere"))) yield Request.Move(by, d, into)
  }

object sharingCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/sharing", extensions = List(frflow.agent.Agent))
