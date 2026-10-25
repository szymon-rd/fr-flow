package sharing

import cats.effect.{IO, SyncIO}
import frflow.*
import frflow.api.{FrFlowError, LiveApi}
import frflow.check.Workspace
import java.net.URI
import java.net.http.{HttpClient, HttpRequest, HttpResponse}
import java.nio.file.Paths
import scala.util.Random
import sharing.Demo.*
import sharing.audit.Audit
import sharing.domain.*
import sharing.housekeeping.{Housekeeping, HousekeepingService}
import sharing.http.*
import sharing.invitations.{Invitations, InvitationsService}
import sharing.notifications.{MemoryMailer, Notifications}
import sharing.ownership.{Ownership, OwnershipService}
import sharing.requests.{AccessRequests, AccessRequestsService}
import sharing.service.{Sharing, SharingService}
import sharing.store.{LibraryStore, MemoryLibraryStore, SqlLibraryStore}
import sharing.time.{ClockKept, Lifetimes}
import sharing.trash.{Trash, TrashService}

class SharingSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout = scala.concurrent.duration.Duration(30, "min")

  private def api =
    LiveApi(knowledge, Workspace(Paths.get("examples/sharing").toAbsolutePath.normalize, "../../../lean"), sys.env.updated("FRFLOW_KEY", "no.key"))
  private def checked = api.flatMap(_.check(None)).recoverWith { case FrFlowError.LeanMissing => IO(assume(false, "lake is not available")) *> IO.never }

  private val contracts = List(Sharing.accessContract, Sharing.canViewContract, Sharing.canEditContract, Sharing.shareContract,
    Sharing.unshareContract, Sharing.moveContract, Invitations.inviteContract, Invitations.acceptContract, Invitations.withdrawContract,
    Trash.trashContract, Trash.restoreContract, Housekeeping.tidyContract, Housekeeping.jobContract, Lifetimes.inForceContract,
    Lifetimes.isOpenContract, Lifetimes.goneContract, SharingHttp.handleContract, AccessRequests.askContract, AccessRequests.approveContract,
    AccessRequests.declineContract, AccessRequests.chaseContract, Ownership.transferContract, Audit.recordContract,
    Notifications.announceContract, Notifications.deliveryJob, Lifetimes.isPendingContract, Lifetimes.reminderDueContract)

  test("the committed ledger accepts every node: none is up for review, none is gone") {
    api.flatMap(_.view).map { v =>
      val states = v.annotated.nodes.map(r => r.id.value -> r.state.toString)
      assertEquals(states.size, knowledge.nodes.size)
      assertEquals(states.filter(_._2 != "accepted"), Nil)
      assertEquals(v.annotated.gone, Nil)
    }
  }

  test("the model is well formed: one timeless root; each feature a branch; the timed words and deadlines below") {
    assertEquals(knowledge.problems, Nil)
    assertEquals(knowledge.root.map(_.id), Some("AccessFollowsShares"))
    def parts(n: frflow.Node[?]) = knowledge.parts(n).map(_.id).toSet
    assertEquals(parts(accessFollowsShares), Set("AccessContract", "CanViewContract", "CanEditContract", "ShareContract", "UnshareContract",
      "MoveContract", "InvitationsAreOffers", "TrashUntilGone", "HousekeepingClearsOnlyTheEnded", "HandleContract",
      "AccessRequestsAreAsks", "OwnersKeepTheirDocuments", "AuditTrail", "NoticesFollowChanges"))
    assertEquals(parts(AccessRequests.requestsAreAsks), Set("AskContract", "ApproveContract", "DeclineContract", "ChaseContract",
      "PendingContract", "ReminderDueContract", "RequestsAnsweredOnTime"))
    assertEquals(parts(Ownership.ownersKeepTheirDocuments), Set("TransferContract", "UnshareContract", "ShareContract"))
    assertEquals(parts(Invitations.invitationsAreOffers), Set("InviteContract", "AcceptContract", "WithdrawContract", "AccessContract",
      "IsOpenContract", "InvitationsLapseOnTime"))
    assertEquals(parts(Trash.trashUntilGone), Set("TrashContract", "RestoreContract", "GoneContract", "TrashPurgedOnTime"))
    assertEquals(parts(Housekeeping.clearsOnlyTheEnded), Set("TidyContract", "EndedStaysEnded"))
    // The branches name no lifetime either: 7 days or 30 days enter only below them.
    for b <- List(Invitations.invitationsAreOffers, Trash.trashUntilGone, Housekeeping.clearsOnlyTheEnded, AccessRequests.requestsAreAsks,
        Ownership.ownersKeepTheirDocuments, Audit.auditTrail, Notifications.noticesFollowChanges) do
      val terms = knowledge.termsOf(b).toSet
      assert(!terms("invitationLasts") && !terms("trashKeeps") && !terms("requestLasts") && !terms("remindAfter"), (b.id, terms))
    assertEquals(knowledge.nodes.filter(_.kind == frflow.protocol.NodeKind.Design).map(_.id), List("ServerWiring", "DomainTypes"))
    // The purpose names no clock and no duration: the lifetimes are open there.
    val rootTerms = knowledge.termsOf(accessFollowsShares).toSet
    assert(!rootTerms("invitationLasts") && !rootTerms("trashKeeps") && !rootTerms("housekeepingWithin"), rootTerms)
  }

  test("the examples pass against the contracts and the code") {
    for n <- contracts do
      assert(knowledge.exampleResults(n).forall(r => r.contract == "ok" && r.implementation.forall(_ == "ok")), (n.id, knowledge.exampleResults(n)))
  }

  test("the boundaries' implementations are run against their models: the memory store and the fake clock tested, SQLite checked") {
    val r = knowledge.test(LibraryStore.libraryKept).get
    assertEquals(r.failure, None)
    assert(r.notes.exists(_.startsWith("MemoryLibraryStore (the project's own code, tested)")), r.notes)
    assert(r.notes.exists(_.startsWith("SqlLibraryStore (an outside system")), r.notes)
    val c = knowledge.test(ClockKept.clockKept).get
    assertEquals(c.failure, None)
    assert(c.notes.exists(_.startsWith("FakeClock")), c.notes)
  }

  test("a seeded bug (plain Scala access that forgets the end of shares) passes some examples; the generated cases find it") {
    val forgetful: (Library, BigInt, PersonId, DocumentId) => Option[Level] = (lib, now, p, d) =>
      if lib.documents.exists(doc => doc.id == d && doc.trashed.isDefined) then None
      else
        val teams = lib.teams.filter(_.members.contains(p)).map(t => Grantee.Team(t.id))
        val places = Target.Doc(d) :: lib.documents.filter(_.id == d).flatMap(_.folders.map(Target.InFolder(_)))
        val mine = lib.shares.filter(s => (s.withWhom == Grantee.Person(p) || teams.contains(s.withWhom)) && places.contains(s.what))
        if mine.exists(_.level == Level.Edit) then Some(Level.Edit) else mine.headOption.map(_ => Level.View)
    val buggy = knowledge.implement(Sharing.accessContract)(forgetful)
    val results = buggy.exampleResults(Sharing.accessContract)
    assert(results.exists(_.implementation.contains("ok")) && results.exists(r => r.implementation.exists(_ != "ok")), results)
    val f = buggy.test(Sharing.accessContract).flatMap(_.failure).get
    assert(f.shown.contains("Some("), f.shown) // shrunk to a share with an end
    println(s"seeded bug found: ${f.shown}")
  }

  test("the services run the proven code: the demo library's answers, over time") {
    assertEquals(SharingService.access(library, now, bob, q3Report), Some(Level.View))
    assertEquals(SharingService.canEdit(library, now, ann, q3Report), true)
    assertEquals(SharingService.canView(library, now, cat, plan), false)
    val shared = SharingService.share(library, now, ann, bobViewsPlanForAnHour)
    assertEquals(SharingService.access(shared, now + 3599, bob, plan), Some(Level.View))
    assertEquals(SharingService.access(shared, now + 3600, bob, plan), None) // ended, before housekeeping ran
    assertEquals(HousekeepingService.tidy(shared, now + 3600), library)
    val invited = InvitationsService.invite(library, now, ann, cat, Target.Doc(plan), Level.View)
    assertEquals(SharingService.access(invited, now, cat, plan), None) // no access until accepted
    assertEquals(SharingService.access(InvitationsService.accept(invited, now + 6 * day, cat, Target.Doc(plan)), now + 6 * day, cat, plan),
      Some(Level.View))
    assertEquals(InvitationsService.accept(invited, now + 7 * day, cat, Target.Doc(plan)), invited) // lapsed
    val trashed = TrashService.trash(library, now, ann, plan)
    assertEquals(SharingService.access(trashed, now, ann, plan), None)
    assertEquals(TrashService.restore(trashed, now + 29 * day, ann, plan), library)
    assertEquals(TrashService.restore(trashed, now + 30 * day, ann, plan), trashed) // gone
    assertEquals(HousekeepingService.tidy(trashed, now + 29 * day).documents.map(_.id), List(plan, q3Report))
    assertEquals(HousekeepingService.tidy(trashed, now + 30 * day).documents.map(_.id), List(q3Report))
    // Access requests: asking gives nothing; an editor approves it; housekeeping reminds, then declines.
    val asked = AccessRequestsService.ask(library, now, cat, plan, Level.View)
    assertEquals(SharingService.access(asked, now, cat, plan), None)
    assertEquals(SharingService.access(AccessRequestsService.approve(asked, now + day, ann, cat, plan), now + day, cat, plan), Some(Level.View))
    assertEquals(AccessRequestsService.approve(asked, now + day, bob, cat, plan), asked)
    assertEquals(AccessRequestsService.chase(asked, now + day), asked)
    val reminded = AccessRequestsService.chase(asked, now + 2 * day)
    assertEquals(reminded.requests.map(_.reminded), List(true))
    assertEquals(reminded.outbox.map(_.to), List(ann))
    assertEquals(AccessRequestsService.chase(reminded, now + 3 * day), reminded) // reminded once
    assertEquals(AccessRequestsService.chase(reminded, now + 7 * day).requests, Nil)
    // Ownership: Ann hands the plan on to Bob once he may edit it; her own share cannot be unshared.
    val bobEdits = SharingService.share(library, now, ann, Share(Target.Doc(plan), Grantee.Person(bob), Level.Edit, None))
    val handed = OwnershipService.transfer(bobEdits, now, ann, plan, bob)
    assertEquals(handed.documents.find(_.id == plan).map(_.owner), Some(bob))
    assertEquals(OwnershipService.transfer(library, now, ann, plan, bob), library)
    assertEquals(SharingService.unshare(bobEdits, now, bob, Target.Doc(plan), Grantee.Person(ann)), bobEdits)
  }

  // ---------------------------------------------------------------------------
  // HTTP: the codec, then the server as a black box against the oracle, on a fake clock
  // ---------------------------------------------------------------------------

  test("the codec reads the routes, refuses what it cannot read with a reason, and knows no other route") {
    assertEquals(HttpCodec.request("GET", "/access", Map("person" -> "bob", "doc" -> "plan"), ""), Right(Request.Access(bob, plan)))
    assertEquals(HttpCodec.request("POST", "/share", Map.empty,
      """{"by":"ann","what":{"folder":"reports"},"with":{"team":"eng"},"level":"edit"}"""),
      Right(Request.Share(ann, Target.InFolder(reports), Grantee.Team(eng), Level.Edit, None)))
    assertEquals(HttpCodec.request("POST", "/share", Map.empty,
      """{"by":"ann","what":{"doc":"plan"},"with":{"person":"bob"},"level":"view","until":1003600}"""),
      Right(Request.Share(ann, Target.Doc(plan), Grantee.Person(bob), Level.View, Some(BigInt(1003600)))))
    assertEquals(HttpCodec.request("POST", "/move", Map.empty, """{"by":"ann","doc":"plan"}"""), Right(Request.Move(ann, plan, None)))
    assertEquals(HttpCodec.request("POST", "/invite", Map.empty, """{"by":"ann","to":"cat","what":{"doc":"plan"},"level":"view"}"""),
      Right(Request.Invite(ann, cat, Target.Doc(plan), Level.View)))
    assertEquals(HttpCodec.request("POST", "/accept", Map.empty, """{"person":"cat","what":{"doc":"plan"}}"""),
      Right(Request.Accept(cat, Target.Doc(plan))))
    assertEquals(HttpCodec.request("POST", "/withdraw", Map.empty, """{"by":"ann","to":"cat","what":{"doc":"plan"}}"""),
      Right(Request.Withdraw(ann, cat, Target.Doc(plan))))
    assertEquals(HttpCodec.request("POST", "/trash", Map.empty, """{"by":"ann","doc":"plan"}"""), Right(Request.Trash(ann, plan)))
    assertEquals(HttpCodec.request("POST", "/restore", Map.empty, """{"by":"ann","doc":"plan"}"""), Right(Request.Restore(ann, plan)))
    assertEquals(HttpCodec.request("GET", "/access", Map("person" -> "bob"), ""), Left(Invalid.Unreadable("doc is missing")))
    assertEquals(HttpCodec.request("POST", "/share", Map.empty, "{"), Left(Invalid.Unreadable("the body is not JSON")))
    assertEquals(HttpCodec.request("POST", "/share", Map.empty, """{"by":"ann","what":{"doc":"plan"},"with":{"person":"bob"},"level":"own"}"""),
      Left(Invalid.Unreadable("level is view or edit, not own")))
    assertEquals(HttpCodec.request("POST", "/share", Map.empty,
      """{"by":"ann","what":{"doc":"plan"},"with":{"person":"bob"},"level":"view","until":"soon"}"""),
      Left(Invalid.Unreadable("until is not a time in seconds")))
    assertEquals(HttpCodec.request("DELETE", "/share", Map.empty, ""), Left(Invalid.NoRoute("DELETE", "/share")))
  }

  private val client = HttpClient.newHttpClient()
  private def send(port: Int, method: String, path: String, body: String = ""): (Int, String) =
    val b = HttpRequest.newBuilder(URI.create(s"http://127.0.0.1:$port$path"))
    val req = if method == "GET" then b.GET() else b.POST(HttpRequest.BodyPublishers.ofString(body))
    val r = client.send(req.build(), HttpResponse.BodyHandlers.ofString())
    (r.statusCode, r.body.trim)

  /** A request line sent as is, over a socket: what `HttpClient` refuses to send. The status line answered. */
  private def raw(port: Int, line: String): String =
    val socket = java.net.Socket("127.0.0.1", port)
    try
      socket.getOutputStream.write(s"$line\r\nHost: localhost\r\nConnection: close\r\n\r\n".getBytes)
      scala.io.Source.fromInputStream(socket.getInputStream).getLines().next()
    finally socket.close()

  private def json(t: Target) = t match
    case Target.Doc(d)      => s"""{"doc":"${d.name}"}"""
    case Target.InFolder(f) => s"""{"folder":"${f.name}"}"""
  private def json(g: Grantee) = g match
    case Grantee.Person(p) => s"""{"person":"${p.name}"}"""
    case Grantee.Team(t)   => s"""{"team":"${t.name}"}"""

  /** A request a client sends, over HTTP, and what the oracle says the server answers; or time passing, or a run of
    * housekeeping, which the test drives through the fake clock's routes.
    */
  private def step(rnd: Random, o: Oracle, clock: FakeClock): (String, String, String, (Int, String)) =
    def pick[A](as: A*): A = as(rnd.nextInt(as.size))
    val now = clock.time
    val p = pick(ann, bob, cat)
    val d = pick(plan, q3Report)
    val t = pick(Target.Doc(plan), Target.Doc(q3Report), Target.InFolder(reports), Target.InFolder(q3))
    val g = pick(Grantee.Person(ann), Grantee.Person(bob), Grantee.Person(cat), Grantee.Team(eng))
    val l = pick(Level.View, Level.Edit)
    def done(ok: Boolean) = if ok then (200, """{"done":true}""") else (403, """{"refused":"you may not make this change"}""")
    rnd.nextInt(16) match
      case 0 | 1 =>
        val level = o.access(now, p, d).fold("none")(_.toString.toLowerCase)
        ("GET", s"/access?person=${p.name}&doc=${d.name}", "", (200, s"""{"access":"$level"}"""))
      case 2 =>
        val until = pick(None, Some(now + 3600), Some(now + 3 * day))
        val field = until.fold("")(u => s""","until":$u""")
        ("POST", "/share", s"""{"by":"${p.name}","what":${json(t)},"with":${json(g)},"level":"${l.toString.toLowerCase}"$field}""",
          done(o.share(now, p, t, g, l, until)))
      case 3 => ("POST", "/unshare", s"""{"by":"${p.name}","what":${json(t)},"with":${json(g)}}""", done(o.unshare(now, p, t, g)))
      case 4 =>
        val into = pick(None, Some(reports), Some(q3), Some(FolderId("nowhere")))
        val field = into.fold("")(f => s""","into":"${f.name}"""")
        ("POST", "/move", s"""{"by":"${p.name}","doc":"${d.name}"$field}""", done(o.move(now, p, d, into)))
      case 5 =>
        val to = pick(ann, bob, cat)
        ("POST", "/invite", s"""{"by":"${p.name}","to":"${to.name}","what":${json(t)},"level":"${l.toString.toLowerCase}"}""",
          done(o.invite(now, p, to, t, l)))
      case 6 => ("POST", "/accept", s"""{"person":"${p.name}","what":${json(t)}}""", done(o.accept(now, p, t)))
      case 7 =>
        val to = pick(ann, bob, cat)
        ("POST", "/withdraw", s"""{"by":"${p.name}","to":"${to.name}","what":${json(t)}}""", done(o.withdraw(now, p, to, t)))
      case 8 => ("POST", "/trash", s"""{"by":"${p.name}","doc":"${d.name}"}""", done(o.trash(now, p, d)))
      case 9 => ("POST", "/restore", s"""{"by":"${p.name}","doc":"${d.name}"}""", done(o.restore(now, p, d)))
      case 12 => ("POST", "/ask", s"""{"person":"${p.name}","doc":"${d.name}","level":"${l.toString.toLowerCase}"}""", done(o.ask(now, p, d, l)))
      case 13 =>
        val who = pick(ann, bob, cat)
        ("POST", "/approve", s"""{"by":"${p.name}","person":"${who.name}","doc":"${d.name}"}""", done(o.approve(now, p, who, d)))
      case 14 =>
        val who = pick(ann, bob, cat)
        ("POST", "/decline", s"""{"by":"${p.name}","person":"${who.name}","doc":"${d.name}"}""", done(o.decline(now, p, who, d)))
      case 15 =>
        val to = pick(ann, bob, cat)
        ("POST", "/transfer", s"""{"by":"${p.name}","doc":"${d.name}","to":"${to.name}"}""", done(o.transfer(now, p, d, to)))
      case 10 =>
        val wait = pick(BigInt(60), BigInt(3600), day, 5 * day, 20 * day)
        ("POST", "/clock", s"""{"advance":$wait}""", (200, s"""{"now":${now + wait}}"""))
      case _ => o.housekeep(now); ("POST", "/housekeep", "", (200, """{"done":true}"""))

  private def blackBox(store: LibraryStore, port: Int, seed: Long): Unit =
    val clock = FakeClock(now)
    val service = StoreHttp(store, clock)
    val (server, workers) = Server.serve(port, service, extra = Server.testing(service, clock, _, _, _))
    try
      val o = Oracle(library)
      val rnd = Random(seed)
      for i <- 1 to 400 do
        val (method, path, body, expected) = step(rnd, o, clock)
        assertEquals(send(port, method, path, body), expected, s"request $i at ${clock.time}: $method $path $body")
    finally { server.stop(0); workers.shutdownNow() }

  test("the server answers 400 generated requests, waits and runs of housekeeping as the oracle written from IDEA.md does, on the memory store") {
    blackBox(MemoryLibraryStore(library), 18731, seed = 1)
  }

  test("and on SQLite") {
    blackBox(SqlLibraryStore.holding(library), 18732, seed = 2)
  }

  test("the server's own answers: 400 with the reason, 404, 503 past the time limit, 500 on an internal error") {
    val slow = new SharingHttp { def handle(r: Request) = { Thread.sleep(2000); Answer.Done } }
    val broken = new SharingHttp { def handle(r: Request) = throw IllegalStateException("store unavailable") }
    val (s1, w1) = Server.serve(18733, StoreHttp(MemoryLibraryStore(library), FakeClock(now)))
    val (s2, w2) = Server.serve(18734, slow, timeoutMs = 200)
    val (s3, w3) = Server.serve(18735, broken)
    try
      assertEquals(send(18733, "GET", "/access?person=bob"), (400, """{"error":"doc is missing"}"""))
      assertEquals(send(18733, "GET", "/nothing"), (404, """{"error":"no route GET /nothing"}"""))
      assertEquals(send(18733, "POST", "/clock", """{"advance":60}"""), (404, """{"error":"no route POST /clock"}"""))
      assert(raw(18733, "GET /access?person=%zz HTTP/1.1").startsWith("HTTP/1.1 400"))
      assertEquals(send(18734, "GET", "/access?person=bob&doc=plan"), (503, """{"error":"over 200 ms"}"""))
      assertEquals(send(18735, "GET", "/access?person=bob&doc=plan"), (500, """{"error":"internal error"}"""))
    finally List((s1, w1), (s2, w2), (s3, w3)).foreach { (s, w) => s.stop(0); w.shutdownNow() }
  }

  /** A session against the server on a fake clock, with failures injected into the store and the mail server: each
    * request and its answer, as a client sees them. What the stage report shows.
    */
  test("a scripted session: a request reminded and declined, a notice retried and delivered once, a 503 that changes nothing, a yes explained") {
    val clock = FakeClock(now)
    val service = StoreHttp(MemoryLibraryStore(library), clock)
    val port = 18736
    val (server, workers) = Server.serve(port, service, extra = Server.testing(service, clock, _, _, _))
    val transcript = List.newBuilder[String]
    def call(method: String, path: String, body: String = ""): (Int, String) =
      val r = send(port, method, path, body)
      transcript += s"$method $path ${body.trim}".trim + s"\n  -> ${r._1} ${r._2}"
      r
    try
      // An access request: no answer for two days, so the owner is reminded; none for seven, so it is declined.
      assertEquals(call("POST", "/ask", """{"person":"cat","doc":"plan","level":"view"}"""), (200, """{"done":true}"""))
      assertEquals(call("GET", "/access?person=cat&doc=plan"), (200, """{"access":"none"}"""))
      call("POST", "/clock", """{"advance":172800}""")
      call("POST", "/housekeep")
      assert(call("GET", "/requests")._2.contains("true"), "reminded")
      call("POST", "/clock", """{"advance":432000}""")
      call("POST", "/housekeep")
      assertEquals(call("GET", "/requests"), (200, "[]"))
      assertEquals(call("POST", "/approve", """{"by":"ann","person":"cat","doc":"plan"}""")._1, 403)
      // Delivery: the outbox holds the notice of the ask (to Ann), the reminder (to Ann) and the decline (to Cat).
      assertEquals(call("GET", "/outbox")._2.split("Notice").length - 1, 3)
      // The mail server is down for three tries: the run fails, the notice stays.
      call("POST", "/faults", """{"fail":[false,true,true,true]}""")
      assertEquals(call("POST", "/deliver")._1, 503)
      assertEquals(call("GET", "/mailbox"), (200, "[]"))
      // Delivered on the second try, but the store fails as the notice leaves the outbox: it stays, and is sent again.
      call("POST", "/faults", """{"fail":[false,true,false,true]}""")
      assertEquals(call("POST", "/deliver")._1, 503)
      assertEquals(call("GET", "/mailbox")._2.split("Notice").length - 1, 1)
      assertEquals(call("POST", "/deliver")._1, 200)
      assertEquals(call("GET", "/mailbox")._2.split("Notice").length - 1, 1) // delivered once
      call("POST", "/deliver"); call("POST", "/deliver")
      assertEquals(call("GET", "/outbox"), (200, "[]"))
      assertEquals(call("GET", "/mailbox")._2.split("Notice").length - 1, 3)
      // A store failure mid-request: 503, and nothing changes.
      call("POST", "/faults", """{"fail":[false,true]}""")
      assertEquals(call("POST", "/share", """{"by":"ann","what":{"doc":"plan"},"with":{"person":"bob"},"level":"view"}"""),
        (503, """{"error":"the store is unavailable: nothing was changed"}"""))
      assertEquals(call("GET", "/access?person=bob&doc=plan"), (200, """{"access":"none"}"""))
      val entries = call("GET", "/log")._2
      assert(!entries.contains("Made(Share("), entries)
      // The same request again: done, and its entry in the log explains Bob's yes.
      assertEquals(call("POST", "/share", """{"by":"ann","what":{"doc":"plan"},"with":{"person":"bob"},"level":"view"}""")._1, 200)
      assertEquals(call("GET", "/access?person=bob&doc=plan"), (200, """{"access":"view"}"""))
      val explained = call("GET", "/log")._2
      assert(explained.contains("""Made(Share(PersonId(\"ann\"), Doc(DocumentId(\"plan\")), Person(PersonId(\"bob\")), View, None))"""), explained)
    finally
      server.stop(0); workers.shutdownNow()
      println(transcript.result().mkString("scripted session:\n", "\n", ""))
  }

  // ---------------------------------------------------------------------------
  // Runs: the service over time, on the fake clock, with the scheduler kept and broken
  // ---------------------------------------------------------------------------

  /** A run of the service: generated requests, waits, and runs of housekeeping at most `period` apart when `kept`
    * (HousekeepingOnTime, with the period a test can afford: the proof holds for any period), or none for weeks when
    * not. After each event: what the deadlines say, measured.
    */
  private final case class Measured(neverEarly: Boolean, trashOnTime: Boolean, invitesOnTime: Boolean, endedGiveNothing: Boolean)
  private def run(seed: Long, kept: Boolean, period: BigInt = 6 * 3600): Measured =
    val rnd = Random(seed)
    def pick[A](as: A*): A = as(rnd.nextInt(as.size))
    val clock = FakeClock(now)
    val store = MemoryLibraryStore(library)
    val service = StoreHttp(store, clock)
    var tidied = clock.time
    var m = Measured(true, true, true, true)
    def housekeep(): Unit =
      val before = store.library
      service.housekeep()
      tidied = clock.time
      val removed = before.documents.filterNot(store.library.documents.contains)
      if !removed.forall(_.trashed.exists(_ + 30 * day <= clock.time)) then m = m.copy(neverEarly = false)
    def measure(): Unit =
      val (lib, t) = (store.library, clock.time)
      if !lib.documents.forall(_.trashed.forall(at => t < at + 30 * day + period)) then m = m.copy(trashOnTime = false)
      if !lib.invitations.forall(i => t < i.sent + 7 * day + period) then m = m.copy(invitesOnTime = false)
      val ended = lib.copy(shares = lib.shares.filter(_.until.forall(t < _)))
      for p <- List(ann, bob, cat); d <- List(plan, q3Report) do
        if SharingService.access(lib, t, p, d) != SharingService.access(ended, t, p, d) then m = m.copy(endedGiveNothing = false)
    for _ <- 1 to 200 do
      val p = pick(ann, bob, cat)
      val t = pick(Target.Doc(plan), Target.Doc(q3Report), Target.InFolder(reports))
      rnd.nextInt(6) match
        case 0 => service.handle(Request.Share(ann, t, Grantee.Person(p), Level.View, pick(None, Some(clock.time + day))))
        case 1 => service.handle(Request.Invite(ann, p, t, Level.View))
        case 2 => service.handle(Request.Accept(p, t))
        case 3 => service.handle(Request.Trash(ann, pick(plan, q3Report)))
        case 4 => service.handle(Request.Restore(ann, pick(plan, q3Report)))
        case _ =>
          // Time passes: days at a time. Kept: housekeeping runs within every period; broken: it does not run.
          var left = pick(day, 3 * day, 10 * day)
          while left > 0 do
            val d = if kept then left.min(tidied + period - clock.time) else left
            clock.advance(d); left -= d
            if kept then housekeep()
      measure()
    if !kept then housekeep()
    m

  test("runs that keep to the scheduler's assumption meet every deadline; never-before and ended shares hold in every run") {
    val keptRuns = (1 to 20).map(s => run(s, kept = true))
    assert(keptRuns.forall(_ == Measured(true, true, true, true)), keptRuns)
    val broken = (1 to 20).map(s => run(100 + s, kept = false))
    // Without housekeeping on time, the bounded responses fail (the deadlines rest on HousekeepingOnTime) ...
    assert(broken.exists(!_.trashOnTime) && broken.exists(!_.invitesOnTime), broken)
    // ... while what rests only on the meaning still holds: nothing is purged early, an ended share gives nothing.
    assert(broken.forall(r => r.neverEarly && r.endedGiveNothing), broken)
  }

  test("the scheduler on a fake clock with adversarial delays: late wake-ups break HousekeepingOnTime, which the server reports") {
    def gaps(delays: List[BigInt]): List[BigInt] =
      val clock = FakeClock(now)
      clock.delay(delays*)
      val starts = List.newBuilder[BigInt]
      Housekeeping.schedule.schedule[SyncIO](clock, times = Some(delays.size + 1), started = starts += _)(() => SyncIO.unit).unsafeRunSync()
      val s = starts.result()
      s.zip(s.tail).map((a, b) => b - a)
    val rnd = Random(7)
    for _ <- 1 to 50 do
      val delays = List.fill(10)(BigInt(rnd.between(0, 120)))
      val g = gaps(delays)
      assertEquals(g, delays.map(_ + 60))
      // HousekeepingOnTime (two minutes) holds exactly when no wake-up is a minute or more late.
      assertEquals(g.forall(_ <= 120), delays.forall(_ <= 60), delays)
  }

  // Runs Lean: `sbt leanTest`, not plain `sbt test`.
  test("the knowledge base is proven, from the code to the root".tag(munit.Tag("Lean"))) {
    for report <- checked
    yield
      val v = report.view
      def node(id: String) = v.node(frflow.protocol.NodeId(id)).map(_.node)
      val statements = v.nodes.filter(_.node.status.isDefined).map(_.id)
      assertEquals(report.nodes.filter(c => statements.contains(c.id)).map(c => c.id -> c.status.toString).toMap, statements.map(_ -> "proven").toMap)
      for c <- contracts do
        assertEquals(node(c.id).flatMap(_.implementationProof).map(_.status.toString), Some("proven"), c.id)
      assertEquals(node("AccessFollowsShares").flatMap(_.rootImpl).map(_.status.toString), Some("proven"))
  }
