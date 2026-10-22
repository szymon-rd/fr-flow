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
    assert(t.contains("Stale (refine)  [rejected: remove it from the model"), t)
    assert(t.contains("Gone  [review: gone]"), t)
  }

  test("decisions are recorded without running the CLI, and refused on stale sources") {
    val p = fake()
    p.run(List("render"), actor = "ui")
    import frflow.Decisions.Request
    assert(p.decide(Request("Inst", "dev", "")).left.exists(_.contains("reason")))
    assertEquals(p.decide(Request("Inst", "dev", "It is simpler.", List("Inst2"))), Right(()))
    val st = p.annotated.get("nodes").get.arr.map(n => s(n, "id") -> s(n, "state")).toMap
    assertEquals((st("Inst"), st("Inst2")), ("accepted", "rejected"))
    assertEquals(p.history.arr.take(2).flatMap(_("node").flatMap(_.str)).toSet, Set("Inst", "Inst2"))
    Files.setLastModifiedTime(p.root.resolve("model.txt"), java.nio.file.attribute.FileTime.fromMillis(System.currentTimeMillis + 5000))
    assert(p.decide(Request("Failed", "dev", "It is still right.")).left.exists(_.contains("render first")))
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

  test("MCP: protocol; the agent settles only what involves no choice, and finds where a change belongs") {
    val p = fake()
    p.run(List("render"), actor = "ui")
    val m = Mcp(List(p))
    val init = m.handle(obj("jsonrpc" -> str("2.0"), "id" -> JNum(1), "method" -> str("initialize"), "params" -> obj())).get
    assertEquals(init("result").flatMap(_("serverInfo")).map(s(_, "name")), Some("frflow"))
    assertEquals(m.handle(obj("jsonrpc" -> str("2.0"), "method" -> str("notifications/initialized"))), None)
    val names = m.tools.map(s(_, "name"))
    assertEquals(names, List("inbox", "context", "render", "check", "answer", "settle", "find", "scaffold"))
    assert(!names.contains("accept"))
    // a root is the developer's to decide
    val (refused, isErr) = call(m, "settle", "node" -> str("Root"), "reason" -> str("It is mechanical enough."))
    assert(isErr && refused.contains("developer"), refused)
    val (found, _) = call(m, "find", "query" -> str("Stale statement"))
    assert(found.contains("Stale"), found)
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
    val server = Server(List(p), "test-token").serve("127.0.0.1", 0)
    try body(s"http://127.0.0.1:${server.getAddress.getPort}", p) finally server.stop(0)

  private def get(url: String): (Int, String) =
    val r = http.send(HttpRequest.newBuilder(URI(url)).build(), HttpResponse.BodyHandlers.ofString(UTF_8))
    (r.statusCode, r.body)

  private def post(url: String, body: Json, headers: (String, String)*): (Int, Json) =
    val b = HttpRequest.newBuilder(URI(url)).POST(HttpRequest.BodyPublishers.ofString(body.compact))
    (Seq("Content-Type" -> "application/json", "X-FrFlow-Token" -> "test-token") ++ headers).toMap.foreach((k, v) => b.header(k, v))
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
      // a process without the browser's session token cannot decide
      assertEquals(post(base + "/api/p/Fake/run", obj("args" -> JArr(Seq(str("render")))), "X-FrFlow-Token" -> "guess")._1, 403)
      val plain = HttpRequest.newBuilder(URI(base + "/api/p/Fake/run")).header("Content-Type", "text/plain").header("X-FrFlow-Token", "test-token")
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

  test("the browser signs the developer's decisions; one written into the ledger otherwise shows") {
    val p = fake()
    val keyFile = Files.createTempDirectory("frflow-key").resolve("signing.key")
    Project.signingKey = Some(frflow.Signing.loadOrCreate(keyFile))
    try
      assert(p.run(List("render"), actor = "ui").ok)
      val root = p.annotated.get("nodes").get.arr.find(n => s(n, "state") == "proposed" && n("waitsFor").contains(JNull)).get
      def version(id: String) = p.snapshot.get("nodes").get.arr.find(n => s(n, "id") == id).map(s(_, "version")).get
      val d = p.decide(frflow.Decisions.Request(s(root, "id"), "dev", "it is the idea, stated", seen = version(s(root, "id"))))
      assert(d.isRight, d)
      val keys = frflow.Signing.keys(p.state.resolve("keys"))
      assertEquals(keys.size, 1)
      // the decision made here is signed; those recorded before the project had a key are listed, to sign
      assert(!p.unsigned.exists(u => s(u, "reason") == "it is the idea, stated"))
      assert(p.unsigned.nonEmpty)
      assert(p.sign(p.unsigned.map(s(_, "entry")).toSet).isRight)
      assertEquals(p.unsigned, Nil)
      // an entry appended by hand, as an agent with a shell could
      val l = p.ledger
      val id = s(root, "id")
      val forged = l.add(id, l.current(id).get.unsigned.copy(at = "2030-01-01T00:00:00Z", reason = "forged by someone"))
      frflow.Ledger.save(p.ledgerFile, forged)
      assertEquals(p.unsigned.map(s(_, "reason")), List("forged by someone"))
      assert(p.annotated.get("warnings").get.arr.exists(_.str.exists(_.contains("not signed by a developer key"))))
      // the developer signs only what is theirs
      assert(p.sign(p.unsigned.map(s(_, "entry")).toSet).isRight)
      assertEquals(p.unsigned, Nil)
      // signing rewrites no recorded decision
      assertEquals(frflow.Ledger.rewrittenSince(forged, p.ledger), Nil)
    finally Project.signingKey = None
  }

  test("the ledger merge driver takes the names git gives it") {
    val base = frflow.Ledger.empty.add("A", frflow.Decision("accept", JNull, "", "dev", "2026-01-01T00:00:00Z", "the first one"))
    val ours = base.add("A", frflow.Decision("revisit", JNull, "", "dev", "2026-01-02T00:00:00Z", "ours revisits it"))
    val theirs = base.add("B", frflow.Decision("accept", JNull, "", "dev", "2026-01-03T00:00:00Z", "theirs adds one"))
    val names = List(".merge_file_base_test", ".merge_file_ours_test", ".merge_file_theirs_test")
    try
      List(base, ours, theirs).zip(names).foreach((l, n) => frflow.Ledger.save(java.nio.file.Paths.get(n), l))
      Main.main(Array("merge-ledger") ++ names)
      val merged = frflow.Ledger.load(java.nio.file.Paths.get(names(1)).toAbsolutePath)
      assertEquals(merged.history("A").map(_.reason), List("the first one", "ours revisits it"))
      assertEquals(merged.history("B").map(_.reason), List("theirs adds one"))
    finally names.foreach(n => Files.deleteIfExists(java.nio.file.Paths.get(n)))
  }


  test("a second key counts only once a developer key certifies it") {
    val dir = Files.createTempDirectory("frflow-keys")
    val (p1, k1) = frflow.Signing.loadOrCreate(Files.createTempDirectory("k1").resolve("key"))
    val (p2, k2) = frflow.Signing.loadOrCreate(Files.createTempDirectory("k2").resolve("key"))
    frflow.Signing.publish(k1, dir)
    assertEquals(frflow.Signing.keys(dir).keySet, Set(frflow.Signing.keyId(k1)))
    // a process that makes its own key and publishes it: not a developer key
    def git(args: String*) = { val pr = ProcessBuilder(("git" +: args)*).directory(dir.toFile).redirectErrorStream(true).start(); pr.getInputStream.readAllBytes(); pr.waitFor() }
    git("init", "-q"); git("config", "user.email", "t@t"); git("config", "user.name", "t"); git("add", "-A"); git("commit", "-qm", "the first key")
    frflow.Signing.publish(k2, dir)
    assertEquals(frflow.Signing.keys(dir).keySet, Set(frflow.Signing.keyId(k1)))
    assertEquals(frflow.Signing.untrusted(dir).size, 1)
    // it cannot certify itself; the developer certifies it, and then it counts
    assert(frflow.Signing.certify(dir, frflow.Signing.keyId(k2), p2, k2).isLeft)
    assert(frflow.Signing.certify(dir, frflow.Signing.keyId(k2), p1, k1).isRight)
    assertEquals(frflow.Signing.keys(dir).keySet, Set(frflow.Signing.keyId(k1), frflow.Signing.keyId(k2)))
    assertEquals(frflow.Signing.untrusted(dir), Nil)
  }
