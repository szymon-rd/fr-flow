package frflow.tools

import frflow.Json
import frflow.Json.*
import java.net.URI
import java.net.http.{HttpClient, HttpRequest, HttpResponse}
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.*

/** The browser server and the MCP server, against a fake knowledge base CLI (a shell script). */
class ToolsSuite extends munit.FunSuite:

  private def fake(): Project =
    val src = Paths.get(getClass.getResource("/fake/frflow.json").toURI).getParent
    val dir = Files.createTempDirectory("frflow-fake").resolve("fake")
    Files.createDirectories(dir)
    Files.list(src).iterator.asScala.foreach(f => Files.copy(f, dir.resolve(f.getFileName)))
    Project(dir)

  private def s(j: Json, k: String) = j(k).flatMap(_.str).getOrElse("")

  test("running the CLI writes the snapshot and records who ran it") {
    val p = fake()
    val r = p.run(List("render"), actor = "agent")
    assert(r.ok, r.output)
    assertEquals(r.output, "ran render")
    assertEquals(p.snapshot.flatMap(_("roots")).map(_.arr.flatMap(_.str)), Some(Seq("Root")))
    assertEquals(p.running, None)
    intercept[IllegalArgumentException](p.run(List("rm"), actor = "agent"))
  }

  test("arguments are quoted for sbt") {
    val p = fake()
    assertEquals(p.command(List("context", "Root", "Ada L")), List("sh", "fake_cli.sh", "context Root \"Ada L\""))
    assertEquals(Project.quote("a;b"), "\"a;b\"")
  }

  test("sources changed after the snapshot") {
    val p = fake()
    assertEquals(p.sourcesChanged, List("(no snapshot yet)"))
    p.run(List("render"), actor = "ui")
    assertEquals(p.sourcesChanged, Nil)
    Files.setLastModifiedTime(p.root.resolve("model.txt"), java.nio.file.attribute.FileTime.fromMillis(System.currentTimeMillis + 5000))
    assertEquals(p.sourcesChanged, List("model.txt"))
  }

  test("the text tree shows decisions (from the ledger), links and examples") {
    val p = fake()
    p.run(List("render"), actor = "ui")
    val t = frflow.Decisions.tree(p.annotated.get)
    assert(t.contains("Root (root)  [accepted]"), t)
    assert(t.contains("  Auto (refine)  [accepted, link proven (auto)]"), t)
    assert(t.contains("    Failed (refine)  [review: above, link failed (must state exactly Obl.link)]"), t)
    assert(t.contains("Contract (contract)  [review: self, code, link proven (authored), examples 2/3]"), t)
    assert(!t.contains("Stale"), t)
    assert(t.contains("Gone  [review: gone]"), t)
  }

  test("decisions are recorded without running the CLI, and refused on stale sources") {
    val p = fake()
    p.run(List("render"), actor = "ui")
    import frflow.Decisions.Request
    assert(p.decide(Request("Inst", "dev", "")).left.exists(_.contains("reason")))
    assertEquals(p.decide(Request("Inst", "dev", "Simpler.", List("Inst2"))), Right(()))
    val st = p.annotated.get("nodes").get.arr.map(n => s(n, "id") -> s(n, "state")).toMap
    assertEquals((st("Inst"), st("Inst2")), ("accepted", "rejected"))
    assertEquals(p.history.arr.take(2).flatMap(_("node").flatMap(_.str)).toSet, Set("Inst", "Inst2"))
    Files.setLastModifiedTime(p.root.resolve("model.txt"), java.nio.file.attribute.FileTime.fromMillis(System.currentTimeMillis + 5000))
    assert(p.decide(Request("Failed", "dev", "Still right.")).left.exists(_.contains("render first")))
  }

  test("requests") {
    val p = fake()
    val id = s(p.addRequest("Auto", "Propose an alternative", "dev"), "id")
    p.answerRequest(id, "Proposed Alt")
    assertEquals((s(p.requests.head, "answer"), s(p.requests.head, "status")), ("Proposed Alt", "answered"))
    p.answerRequest(id, "", "closed")
    assertEquals((s(p.requests.head, "answer"), s(p.requests.head, "status")), ("Proposed Alt", "closed"))
    intercept[java.util.NoSuchElementException](p.answerRequest("R9", "x"))
  }

  // -- MCP --------------------------------------------------------------------

  private def call(m: Mcp, tool: String, args: (String, Json)*): (String, Boolean) =
    val r = m.handle(obj("jsonrpc" -> str("2.0"), "id" -> JNum(1), "method" -> str("tools/call"),
      "params" -> obj("name" -> str(tool), "arguments" -> JObj(args)))).get("result").get
    (r("content").get.arr.head("text").flatMap(_.str).get, r("isError").contains(JBool(true)))

  test("MCP: protocol, and no tool to accept") {
    val m = Mcp(List(fake()))
    val init = m.handle(obj("jsonrpc" -> str("2.0"), "id" -> JNum(1), "method" -> str("initialize"), "params" -> obj())).get
    assertEquals(init("result").flatMap(_("serverInfo")).map(s(_, "name")), Some("frflow"))
    assertEquals(m.handle(obj("jsonrpc" -> str("2.0"), "method" -> str("notifications/initialized"))), None)
    val names = m.tools.map(s(_, "name"))
    assertEquals(names, List("inbox", "context", "render", "check", "answer", "scaffold"))
    val err = m.handle(obj("jsonrpc" -> str("2.0"), "id" -> JNum(2), "method" -> str("nope"))).get
    assertEquals(err("error").flatMap(_("code")), Some(JNum(-32601)))
  }

  test("MCP: render, inbox, answer") {
    val p = fake()
    val m = Mcp(List(p))
    assert(call(m, "inbox")._1.contains("No snapshot yet"))
    val (out, err) = call(m, "render")
    assert(!err && out.contains("Contract (contract)"), out)
    val id = s(p.addRequest("Auto", "Propose an alternative to Auto", "dev"), "id")
    val inbox = call(m, "inbox")._1
    assert(inbox.contains(s"[$id] on Auto: Propose an alternative to Auto"), inbox)
    assert(inbox.contains("Stale: rejected; remove it"), inbox)
    assert(inbox.contains("Inst: proposed"), inbox)
    assert(inbox.contains("Gone: gone from the model"), inbox)
    assert(!call(m, "answer", "request" -> str(id), "text" -> str("Proposed Alt"))._2)
    assertEquals(s(p.requests.head, "status"), "answered")
    assert(call(m, "context", "node" -> str("A;B"))._2)
  }

  // -- the browser server -----------------------------------------------------

  private val http = HttpClient.newHttpClient()

  private def withServer(body: (String, Project) => Unit): Unit =
    val p = fake()
    val server = Server(List(p)).serve("127.0.0.1", 0)
    try body(s"http://127.0.0.1:${server.getAddress.getPort}", p) finally server.stop(0)

  private def get(url: String): (Int, String) =
    val r = http.send(HttpRequest.newBuilder(URI(url)).build(), HttpResponse.BodyHandlers.ofString(UTF_8))
    (r.statusCode, r.body)

  private def post(url: String, body: Json, headers: (String, String)*): (Int, Json) =
    val b = HttpRequest.newBuilder(URI(url)).POST(HttpRequest.BodyPublishers.ofString(body.compact))
    (("Content-Type" -> "application/json") +: headers).toMap.foreach((k, v) => b.header(k, v))
    val r = http.send(b.build(), HttpResponse.BodyHandlers.ofString(UTF_8))
    (r.statusCode, Json.parse(r.body))

  test("server: the page, the snapshot, and running commands") {
    withServer { (base, p) =>
      assert(get(base + "/")._2.contains("FrFlow"))
      assertEquals(Json.parse(get(base + "/api/projects")._2).arr.map(s(_, "name")), Seq("Fake"))
      assertEquals(Json.parse(get(base + "/api/p/Fake/kb")._2)("snapshot"), Some(JNull))
      assertEquals(post(base + "/api/p/Fake/run", obj("args" -> JArr(Seq(str("render")))))._1, 202)
      var job = Json.parse(get(base + "/api/p/Fake/job")._2)
      var n = 0
      while job("running").contains(JBool(true)) && n < 100 do { Thread.sleep(50); n += 1; job = Json.parse(get(base + "/api/p/Fake/job")._2) }
      assertEquals(job("exitCode"), Some(JNum(0)), job("output"))
      assertEquals(Json.parse(get(base + "/api/p/Fake/kb")._2)("snapshot").flatMap(_("nodes")).map(_.arr.size), Some(8))
      assertEquals(Json.parse(get(base + "/api/p/Fake/history")._2).arr.size, 7)
    }
  }

  test("server: commands are restricted, other sites cannot post") {
    withServer { (base, _) =>
      def run(args: String*) = post(base + "/api/p/Fake/run", obj("args" -> JArr(args.map(str))))._1
      assertEquals(run("status"), 400)
      assertEquals(run("accept", "Root", "--by", "me"), 400)
      assertEquals(run("scaffold", "Root;x"), 400)
      assertEquals(post(base + "/api/p/Fake/decide", obj("action" -> str("accept"), "node" -> str("Root;x"), "by" -> str("me"), "reason" -> str("r")))._1, 400)
      assertEquals(post(base + "/api/p/Nope/run", obj("args" -> JArr(Seq(str("render")))))._1, 404)
      assertEquals(post(base + "/api/p/Fake/run", obj("args" -> JArr(Seq(str("render")))), "Origin" -> "http://evil.example")._1, 403)
      val plain = HttpRequest.newBuilder(URI(base + "/api/p/Fake/run")).header("Content-Type", "text/plain")
        .POST(HttpRequest.BodyPublishers.ofString("""{"args":["render"]}""")).build()
      assertEquals(http.send(plain, HttpResponse.BodyHandlers.ofString()).statusCode, 415)
    }
  }

  test("server: requests and the idea") {
    withServer { (base, p) =>
      val (st, r) = post(base + "/api/p/Fake/requests", obj("node" -> str("Auto"), "text" -> str("Propose another"), "by" -> str("dev")))
      assertEquals(st, 201)
      assertEquals(Json.parse(get(base + "/api/p/Fake/kb")._2)("requests").map(_.arr.map(s(_, "text"))), Some(Seq("Propose another")))
      assertEquals(s(post(base + s"/api/p/Fake/requests/${s(r, "id")}", obj("status" -> str("closed")))._2, "status"), "closed")
      assertEquals(post(base + "/api/p/Fake/idea", obj("text" -> str("# New idea")))._1, 200)
      assertEquals(Files.readString(p.root.resolve("IDEA.md")), "# New idea\n")
    }
  }
