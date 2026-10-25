package sharing

import cats.effect.IO
import frflow.*
import frflow.api.{FrFlowError, LiveApi}
import frflow.check.Workspace
import java.net.URI
import java.net.http.{HttpClient, HttpRequest, HttpResponse}
import java.nio.file.Paths
import scala.util.Random
import sharing.Demo.*
import sharing.domain.*
import sharing.http.*
import sharing.service.{Sharing, SharingService}
import sharing.store.{LibraryStore, MemoryLibraryStore, SqlLibraryStore}

class SharingSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout = scala.concurrent.duration.Duration(30, "min")

  private def api =
    LiveApi(knowledge, Workspace(Paths.get("examples/sharing").toAbsolutePath.normalize, "../../../lean"), sys.env.updated("FRFLOW_KEY", "no.key"))
  private def checked = api.flatMap(_.check(None)).recoverWith { case FrFlowError.LeanMissing => IO(assume(false, "lake is not available")) *> IO.never }

  test("the committed ledger accepts every node: none is up for review, none is gone") {
    api.flatMap(_.view).map { v =>
      val states = v.annotated.nodes.map(r => r.id.value -> r.state.toString)
      assertEquals(states.size, knowledge.nodes.size)
      assertEquals(states.filter(_._2 != "accepted"), Nil)
      assertEquals(v.annotated.gone, Nil)
    }
  }

  test("the model is well formed: one root, Sharing's six contracts and the HTTP handling under it") {
    assertEquals(knowledge.problems, Nil)
    assertEquals(knowledge.root.map(_.id), Some("AccessFollowsShares"))
    assertEquals(knowledge.parts(accessFollowsShares).map(_.id), List("AccessContract", "CanViewContract", "CanEditContract",
      "ShareContract", "UnshareContract", "MoveContract", "HandleContract"))
    assertEquals(knowledge.nodes.filter(_.kind == frflow.protocol.NodeKind.Design).map(_.id), List("ServerWiring", "DomainTypes"))
  }

  test("the examples pass against the contracts and the code") {
    for n <- List(Sharing.accessContract, Sharing.canViewContract, Sharing.canEditContract, Sharing.shareContract, Sharing.unshareContract,
        Sharing.moveContract, SharingHttp.handleContract) do
      assert(knowledge.exampleResults(n).forall(r => r.contract == "ok" && r.implementation.forall(_ == "ok")), knowledge.exampleResults(n))
  }

  test("the store's implementations are run against its model: the memory store tested, SQLite checked") {
    val r = knowledge.test(LibraryStore.libraryKept).get
    assertEquals(r.failure, None)
    assert(r.notes.exists(_.startsWith("MemoryLibraryStore (the project's own code, tested)")), r.notes)
    assert(r.notes.exists(_.startsWith("SqlLibraryStore (an outside system")), r.notes)
  }

  test("a seeded bug (plain Scala access that forgets teams) passes some examples; the generated cases find it, shrunk") {
    val forgetful: (Library, PersonId, DocumentId) => Option[Level] = (lib, p, d) =>
      val mine = lib.shares.filter(s => s.withWhom == Grantee.Person(p) &&
        (s.what == Target.Doc(d) || lib.documents.exists(doc => doc.id == d && s.what.match { case Target.InFolder(f) => doc.folders.contains(f); case _ => false })))
      if mine.exists(_.level == Level.Edit) then Some(Level.Edit) else mine.headOption.map(_ => Level.View)
    val buggy = knowledge.implement(Sharing.accessContract)(forgetful)
    val results = buggy.exampleResults(Sharing.accessContract)
    assert(results.exists(_.implementation.contains("ok")) && results.exists(r => r.implementation.exists(_ != "ok")), results)
    val f = buggy.test(Sharing.accessContract).flatMap(_.failure).get
    // shrunk to a share with a team the person is in
    assert(f.shown.contains("Team"), f.shown)
    println(s"seeded bug found: ${f.shown}")
  }

  test("SharingService runs the proven code: the demo library's answers") {
    assertEquals(SharingService.access(library, bob, q3Report), Some(Level.View))
    assertEquals(SharingService.canEdit(library, ann, q3Report), true)
    assertEquals(SharingService.canView(library, cat, plan), false)
    val moved = SharingService.move(library, ann, plan, Some(q3))
    assertEquals(moved.documents.find(_.id == plan).map(_.folders), Some(List(reports, q3)))
    assertEquals(SharingService.access(moved, bob, plan), Some(Level.View))
  }

  // ---------------------------------------------------------------------------
  // HTTP: the codec, then the server as a black box against the oracle
  // ---------------------------------------------------------------------------

  test("the codec reads the routes, refuses what it cannot read with a reason, and knows no other route") {
    assertEquals(HttpCodec.request("GET", "/access", Map("person" -> "bob", "doc" -> "plan"), ""), Right(Request.Access(bob, plan)))
    assertEquals(HttpCodec.request("POST", "/share", Map.empty,
      """{"by":"ann","what":{"folder":"reports"},"with":{"team":"eng"},"level":"edit"}"""),
      Right(Request.Share(ann, Target.InFolder(reports), Grantee.Team(eng), Level.Edit)))
    assertEquals(HttpCodec.request("POST", "/move", Map.empty, """{"by":"ann","doc":"plan"}"""), Right(Request.Move(ann, plan, None)))
    assertEquals(HttpCodec.request("GET", "/access", Map("person" -> "bob"), ""), Left(Invalid.Unreadable("doc is missing")))
    assertEquals(HttpCodec.request("POST", "/share", Map.empty, "{"), Left(Invalid.Unreadable("the body is not JSON")))
    assertEquals(HttpCodec.request("POST", "/share", Map.empty, """{"by":"ann","what":{"doc":"plan"},"with":{"person":"bob"},"level":"own"}"""),
      Left(Invalid.Unreadable("level is view or edit, not own")))
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

  /** A request a client sends, over HTTP, and what the oracle says the server answers. */
  private def step(rnd: Random, o: Oracle): (String, String, String, (Int, String)) =
    def pick[A](as: A*): A = as(rnd.nextInt(as.size))
    val p = pick(ann, bob, cat)
    val d = pick(plan, q3Report)
    val t = pick(Target.Doc(plan), Target.Doc(q3Report), Target.InFolder(reports), Target.InFolder(q3))
    val g = pick(Grantee.Person(ann), Grantee.Person(bob), Grantee.Person(cat), Grantee.Team(eng))
    val l = pick(Level.View, Level.Edit)
    def done(ok: Boolean) = if ok then (200, """{"done":true}""") else (403, """{"refused":"you may not edit it"}""")
    rnd.nextInt(5) match
      case 0 | 1 =>
        val level = o.access(p, d).fold("none")(_.toString.toLowerCase)
        ("GET", s"/access?person=${p.name}&doc=${d.name}", "", (200, s"""{"access":"$level"}"""))
      case 2 =>
        ("POST", "/share", s"""{"by":"${p.name}","what":${json(t)},"with":${json(g)},"level":"${l.toString.toLowerCase}"}""", done(o.share(p, t, g, l)))
      case 3 => ("POST", "/unshare", s"""{"by":"${p.name}","what":${json(t)},"with":${json(g)}}""", done(o.unshare(p, t, g)))
      case _ =>
        val into = pick(None, Some(reports), Some(q3), Some(FolderId("nowhere")))
        val field = into.fold("")(f => s""","into":"${f.name}"""")
        ("POST", "/move", s"""{"by":"${p.name}","doc":"${d.name}"$field}""", done(o.move(p, d, into)))

  private def blackBox(store: LibraryStore, port: Int, seed: Long): Unit =
    val (server, workers) = Server.serve(port, StoreHttp(store))
    try
      val o = Oracle(library)
      val rnd = Random(seed)
      for i <- 1 to 300 do
        val (method, path, body, expected) = step(rnd, o)
        assertEquals(send(port, method, path, body), expected, s"request $i: $method $path $body")
    finally { server.stop(0); workers.shutdownNow() }

  test("the server answers 300 generated requests as the oracle written from IDEA.md does, on the memory store") {
    blackBox(MemoryLibraryStore(library), 18731, seed = 1)
  }

  test("and on SQLite") {
    blackBox(SqlLibraryStore.holding(library), 18732, seed = 2)
  }

  test("the server's own answers: 400 with the reason, 404, 503 past the time limit, 500 on an internal error") {
    val slow = new SharingHttp { def handle(r: Request) = { Thread.sleep(2000); Answer.Done } }
    val broken = new SharingHttp { def handle(r: Request) = throw IllegalStateException("store unavailable") }
    val (s1, w1) = Server.serve(18733, StoreHttp(MemoryLibraryStore(library)))
    val (s2, w2) = Server.serve(18734, slow, timeoutMs = 200)
    val (s3, w3) = Server.serve(18735, broken)
    try
      assertEquals(send(18733, "GET", "/access?person=bob"), (400, """{"error":"doc is missing"}"""))
      assertEquals(send(18733, "GET", "/nothing"), (404, """{"error":"no route GET /nothing"}"""))
      assert(raw(18733, "GET /access?person=%zz HTTP/1.1").startsWith("HTTP/1.1 400"))
      assertEquals(send(18734, "GET", "/access?person=bob&doc=plan"), (503, """{"error":"over 200 ms"}"""))
      assertEquals(send(18735, "GET", "/access?person=bob&doc=plan"), (500, """{"error":"internal error"}"""))
    finally List((s1, w1), (s2, w2), (s3, w3)).foreach { (s, w) => s.stop(0); w.shutdownNow() }
  }

  // Runs Lean: `sbt leanTest`, not plain `sbt test`.
  test("the knowledge base is proven, from the code to the root".tag(munit.Tag("Lean"))) {
    for report <- checked
    yield
      val v = report.view
      def node(id: String) = v.node(frflow.protocol.NodeId(id)).map(_.node)
      val statements = v.nodes.filter(_.node.status.isDefined).map(_.id)
      assertEquals(report.nodes.filter(c => statements.contains(c.id)).map(c => c.id -> c.status.toString).toMap, statements.map(_ -> "proven").toMap)
      for c <- List("AccessContract", "CanViewContract", "CanEditContract", "ShareContract", "UnshareContract", "MoveContract", "HandleContract") do
        assertEquals(node(c).flatMap(_.implementationProof).map(_.status.toString), Some("proven"), c)
      assertEquals(node("AccessFollowsShares").flatMap(_.rootImpl).map(_.status.toString), Some("proven"))
  }
