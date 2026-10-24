package rebac

import frflow.*
import cats.effect.IO
import frflow.api.{FrFlowError, LiveApi}
import frflow.check.Workspace
import java.nio.file.Paths

class RebacSuite extends munit.CatsEffectSuite:
  // The API over the example's own workspace; nothing here decides, so no key is read.
  private def api =
    LiveApi(knowledge, Workspace(Paths.get("examples/rebac").toAbsolutePath.normalize, "../../../lean"), sys.env.updated("FRFLOW_KEY", "no.key"))

  private def checked = api.flatMap(_.check(None)).recoverWith { case FrFlowError.LeanMissing => IO(assume(false, "lake is not available")) *> IO.never }
  override val munitIOTimeout = scala.concurrent.duration.Duration(30, "min")

  // Runs Lean: `sbt leanTest`, not plain `sbt test`.
  test("the knowledge base is proven from the code to the root: the recursive resolution, and the cached check".tag(munit.Tag("Lean"))) {
    checked.map { report =>
      assertEquals(report.nodes.map(c => c.id.value -> c.status.toString).filter(_._2 != "proven"), Nil)
      assertEquals(report.view.snapshot.root.flatMap(report.view.node).flatMap(_.node.rootImpl).map(_.status.toString), Some("proven"))
      // root_impl rests on the store's index, an assumption: the check and the cache are proven of their code
      assertEquals(report.view.snapshot.trusted, List(frflow.protocol.NodeId(storeIndex.id)))
    }
  }

  test("the committed ledger accepts every node: none is up for review, none is gone") {
    api.flatMap(_.view).map { v =>
      val states = v.annotated.nodes.map(r => r.id.value -> r.state.toString)
      assertEquals(states.size, knowledge.nodes.size)
      assertEquals(states.filter(_._2 != "accepted"), Nil)
      assertEquals(v.annotated.gone, Nil)
    }
  }

  test("the model is well formed: the meaning in two definitions, the root split into the resolution and the two indexes it reads") {
    assertEquals(knowledge.problems, Nil)
    assertEquals(knowledge.root.map(_.id), Some("ChecksExactly"))
    assertEquals(knowledge.definitions.map(_.id), List("Versions", "Derivation"))
    assertEquals(knowledge.parts(checksExactly).map(_.id), List("StoreIndex", "SchemaIndex", "CheckContract"))
  }

  test("the examples pass against the contracts, the indexes and the code, and on the cache's own implementation") {
    for n <- List(checkContract, storeIndex, schemaIndex, cachedChecks) do
      assert(knowledge.exampleResults(n).forall(r => r.contract == "ok" && r.implementation.forall(_ == "ok")), knowledge.exampleResults(n))
  }

  test("the store's and the schema's indexes, and the running resolution, are checked against their proven code on generated data") {
    for n <- List(storeIndex, schemaIndex, checkContract) do
      val r = knowledge.test(n).get
      assertEquals(r.failure, None, n.id)
  }

  test("the cache is tested against its model on generated runs of its operations") {
    val r = knowledge.test(cacheKeepsAnswers).get
    assertEquals(r.failure, None)
    assert(r.notes.exists(_.startsWith("LruCache (the project's own code, tested)")), r.notes)
  }

  test("a seeded bug in the cache (answers kept by check only, not by version) is found by generated runs and shrunk") {
    // The classic stale-cache bug: a later version is answered with an earlier version's answer.
    final class StaleCache(start: List[Cached]) extends AnswerCache:
      private var kept: List[(Query, Cached)] = start.map(c => c.ask.query -> c)
      def entries: List[Cached] = kept.map(_._2)
      def lookup(a: Term[Ask]) = Flow.effect(a)(ask => kept.find(_._1 == ask.query).map(_._2.answer))
      def remember(a: Term[Ask], answer: Term[Boolean]) = Flow.effect(a, answer) { (ask, b) =>
        kept = ((ask.query -> Cached(ask, b)) :: kept.filterNot(_._1 == ask.query)).take(cacheSize)
      }
    val stale = Node.assumption(rebac.cache)(CacheModel)("CacheKeepsAnswers", cacheKeepsAnswers.statement, cacheKeepsAnswers.why)
      .implementedBy(cs => StaleCache(cs), _.entries)
    val kb = KnowledgeBase(knowledge.name, knowledge.idea, knowledge.implementations, knowledge.generators, knowledge.testing)(
      knowledge.nodes.map(n => if n eq cacheKeepsAnswers then stale else n)*)
    val f = kb.test(stale).get.failure.get
    assert(f.shown.startsWith("on StaleCache, from "), f.shown)
    println(s"stale cache, shrunk: ${f.shown} — ${f.why}")
  }

  test("a seeded bug in the store (deletes ignored) is found by the generated logs of writes, and shrunk") {
    val ignoringDeletes = KnowledgeBase(knowledge.name, knowledge.idea, knowledge.implementations, knowledge.generators, knowledge.testing)(
      knowledge.nodes*).implementProven(storeIndex)(storedOf, (v, o) =>
        TupleStore.replaying(writes.value.filter { case Write.Add(_) => true; case _ => false }).tuplesOf(v, o))
    val f = ignoringDeletes.test(storeIndex).flatMap(_.failure)
    assert(f.isDefined, "a store that ignores deletes passed")
    f.foreach(x => println(s"store ignoring deletes, shrunk: ${x.shown} — ${x.why}"))
  }

  test("the tuples of a version never change when later writes are added: what keeps a kept answer the check's") {
    val r = scala.util.Random(7)
    def tuple() = RelTuple(Obj("doc", s"d${r.nextInt(3)}"), List("viewer", "editor")(r.nextInt(2)), Subject.Person(s"u${r.nextInt(3)}"))
    def log(n: Int) = List.fill(n)(if r.nextBoolean() then Write.Add(tuple()) else Write.Remove(tuple()))
    for _ <- 1 to 200 do
      val (ws, more) = (log(r.nextInt(8)), log(r.nextInt(4)))
      for v <- 0 to ws.size do assertEquals(tuplesAt.fn(ws ++ more, v), tuplesAt.fn(ws, v), (ws, more, v))
  }

  test("the running store is found again by its log, not rebuilt on each read") {
    val s = TupleStore.replaying(demoWrites)
    assert(TupleStore.of(s.writes) eq s)
    assertEquals(TupleStore.of(demoWrites.map(identity)).tuplesOf(2, readme), s.tuplesOf(2, readme))
  }

  test("the service: writes get versions, a check answers by the tuples of its version, and a kept answer survives later writes") {
    val s = RebacService(demoSchema, serviceLevels)
    demoWrites.take(3).foreach(s.write)
    val ann = Query(readme, "viewer", "ann")
    assertEquals(s.allowed(ann, 3), true)
    demoWrites.drop(3).foreach(s.write)
    assertEquals(List(0, 1, 2, 3, 4, 5).map(v => s.allowed(ann, v)), List(false, false, false, true, true, false))
    assertEquals(s.allowed(Query(readme, "viewer", "bob"), s.latest), true)
    assertEquals(s.allowed(Query(readme, "editor", "ann"), 3), false)
    intercept[IllegalArgumentException](s.allowed(ann, 6)) // never past the latest
  }

  test("a schema defining a kind and relation twice is refused: which definition would a check read?") {
    val twice = demoSchema :+ RelationDef("doc", "viewer", List(Rule.Direct))
    assertEquals(Schema.problems(twice), List("doc#viewer is defined 2 times"))
    assertEquals(Schema.problems(demoSchema), Nil)
    intercept[IllegalArgumentException](RebacService(twice, serviceLevels))
  }

  test("the cache keeps at most cacheSize answers: the newest, the oldest dropped") {
    val c = LruCache.holding(Nil)
    val asks = (0 until cacheSize + 5).map(i => Ask(Query(readme, "viewer", s"u$i"), 1))
    asks.foreach(a => c.put(a, true))
    assertEquals(c.entries.size, cacheSize)
    assertEquals(c.entries.head.ask, asks.last)
    assertEquals(asks.take(5).toList.map(c.get), List.fill(5)(Option.empty[Boolean]))
    assertEquals(c.get(asks(5)), Some(true))
  }

  // k groups that are all members of each other: a check for someone in none of them explores every path unless it
  // remembers what it already answered.
  private def cycle(k: Int): List[Write] =
    (for i <- 0 until k; j <- 0 until k if i != j
    yield Write.Add(RelTuple(Obj("group", s"c$i"), "member", Subject.Members(Obj("group", s"c$j"), "member")))).toList

  test("a cycle of groups: the running resolution remembers each step, and answers in milliseconds at OpenFGA's depth") {
    for k <- List(3, 6, 12) do
      val s = RebacService(demoSchema, serviceLevels)
      (cycle(k) :+ Write.Add(RelTuple(Obj("group", s"c${k - 1}"), "member", Subject.Person("zed")))).foreach(s.write)
      val t0 = System.nanoTime
      assertEquals(s.allowed(Query(Obj("group", "c0"), "member", "nobody"), s.latest), false)
      assertEquals(s.allowed(Query(Obj("group", "c0"), "member", "zed"), s.latest), true)
      val ms = (System.nanoTime - t0) / 1000000
      assert(ms < 2000, s"$k groups in a cycle took $ms ms")
  }

  test("the HTTP layer is tested against its protocol on generated runs of requests, every part of the protocol reached") {
    val r = knowledge.test(httpProtocol).get
    assertEquals(r.failure, None)
    assertEquals(r.coverage.filter(_.held == 0).map(_.part), Nil)
  }

  /** The protocol's test of an HTTP layer with a seeded bug, put in the node in place of the layer: the failure, shrunk. */
  private def seeded(bug: (HttpLayer, Request) => Reply): Option[String] =
    final class Bugged(table: TableHttp.Table) extends HttpLayer(table):
      private val inner = HttpLayer(table)
      override def respond(r: Request): Reply = bug(inner, r)
      def served: Served = table.served
    val node = Node.assumption(rebac.http)(HttpModel)("HttpProtocol", httpProtocol.statement, httpProtocol.why)
      .implementedBy(s => Bugged(TableHttp.Table(s)), _.served)
    val kb = KnowledgeBase(knowledge.name, knowledge.idea, knowledge.implementations, knowledge.generators, knowledge.testing)(
      knowledge.nodes.map(n => if n eq httpProtocol then node else n)*)
    kb.test(node).flatMap(_.failure).map(f => s"${f.shown} — ${f.why}")

  test("seeded bugs in the HTTP layer are found by the protocol's generated runs, and shrunk: the answer inverted; write and delete swapped") {
    val inverted = seeded((l, r) => { val x = l.respond(r); x.copy(answer = x.answer.map(!_)) })
    assert(inverted.isDefined, "an inverted answer passed")
    val swapped = seeded((l, r) => l.respond(r match
      case Request.Add(g)    => Request.Delete(g)
      case Request.Delete(g) => Request.Add(g)
      case other             => other))
    assert(swapped.isDefined, "write and delete swapped passed")
    println(s"inverted answer, shrunk: ${inverted.get}\nwrite and delete swapped, shrunk: ${swapped.get}")
  }

  test("requests are validated: relations the schema declares, versions from 0 to the latest, a person named; the version is returned") {
    val s = RebacService(demoSchema, serviceLevels)
    val layer = HttpLayer(s)
    def call(m: String, path: String, params: (String, String)*) = RebacHttp.answer(layer, m, path, params.toMap)
    assertEquals(call("POST", "/write", "tuple" -> "group:eng#member@user:ann")._1, 200)
    assertEquals(call("POST", "/write", "tuple" -> "doc:x#veiwer@user:typo"),
      (400, "the schema declares no relation veiwer on doc", Map("Rebac-Version" -> "1")))
    assertEquals(call("POST", "/write", "tuple" -> "folder:eng#viewer@group:eng#membr")._2, "the schema declares no relation membr on group")
    assertEquals(call("GET", "/check", "tuple" -> "group:eng#member@user:ann"), (200, "yes", Map("Rebac-Version" -> "1")))
    assertEquals(call("GET", "/check", "tuple" -> "group:eng#member@user:ann", "at" -> "0"), (200, "no", Map("Rebac-Version" -> "0")))
    for at <- List("abc", "-1", "2", "99999999999999999999") do
      assertEquals(call("GET", "/check", "tuple" -> "group:eng#member@user:ann", "at" -> at)._1, 400, at)
    assertEquals(call("GET", "/check", "tuple" -> "group:eng#member@user:ann", "at" -> "2")._2, "at must be a version from 0 to 1")
    assertEquals(call("GET", "/check", "tuple" -> "group:eng#member@user:")._1, 400)
    assertEquals(call("GET", "/check", "tuple" -> "doc:readme#viewer@group:eng#member")._2, "a check names a person: doc:readme#viewer@user:ann")
    assertEquals(call("GET", "/nope")._1, 404)
    assertEquals(s.latest, 1) // nothing refused was written
  }

  test("tuple strings: users, usersets and links parse and print back; anything else is refused with a reason") {
    val ok = List(
      "doc:readme#viewer@user:ann" -> RelTuple(readme, "viewer", Subject.Person("ann")),
      "folder:eng#viewer@group:eng#member" -> RelTuple(eng, "viewer", Subject.Members(engGroup, "member")),
      "doc:readme#parent@>folder:eng" -> RelTuple(readme, "parent", Subject.Link(eng)))
    for (text, t) <- ok do
      assertEquals(TupleSyntax.parse(text), Right(t))
      assertEquals(TupleSyntax.show(t), text)
    for bad <- List("", "doc:readme", "doc:readme#viewer", "doc#viewer@user:ann", "doc:readme#viewer@ann", "doc:readme#@user:ann",
        "doc:readme#viewer@group:eng#", "doc:readme#viewer@user:") do
      assert(TupleSyntax.parse(bad).isLeft, bad)
  }

  private def http(server: com.sun.net.httpserver.HttpServer) =
    val client = java.net.http.HttpClient.newHttpClient()
    (m: String, pathAndQuery: String) =>
      val req = java.net.http.HttpRequest.newBuilder(java.net.URI.create(s"http://127.0.0.1:${server.getAddress.getPort}$pathAndQuery"))
        .method(m, java.net.http.HttpRequest.BodyPublishers.noBody()).build()
      val res = client.send(req, java.net.http.HttpResponse.BodyHandlers.ofString())
      (res.statusCode, res.body.trim, res.headers.firstValue("Rebac-Version").orElse(""))
  private def enc(t: String) = java.net.URLEncoder.encode(t, "UTF-8")

  test("black box over HTTP: random writes, deletes and checks, with cycles, against an oracle written from IDEA.md") {
    val server = RebacHttp.serve(0, RebacService(demoSchema, serviceLevels))
    try
      val call = http(server)
      val oracle = Oracle(demoSchema, serviceLevels.size)
      val r = scala.util.Random(11)
      def pick[A](xs: A*) = xs(r.nextInt(xs.size))
      def doc = Obj("doc", s"d${r.nextInt(3)}")
      def folder = Obj("folder", s"f${r.nextInt(2)}")
      def group = Obj("group", s"g${r.nextInt(3)}")
      def user = s"u${r.nextInt(3)}"
      def tuple(): RelTuple = r.nextInt(6) match
        case 0 => RelTuple(doc, pick("viewer", "editor"), Subject.Person(user))
        case 1 => RelTuple(doc, "parent", Subject.Link(folder))
        case 2 => RelTuple(folder, "viewer", Subject.Members(group, "member"))
        case 3 => RelTuple(group, "member", Subject.Members(group, "member")) // cycles too
        case _ => RelTuple(group, "member", Subject.Person(user))
      val written = scala.collection.mutable.ArrayBuffer.empty[RelTuple]
      var checks = 0
      for _ <- 1 to 400 do
        r.nextInt(10) match
          case 0 | 1 | 2 =>
            val t = tuple()
            written += t
            assertEquals(call("POST", s"/write?tuple=${enc(TupleSyntax.show(t))}")._2, oracle.write(true, t).toString)
          case 3 =>
            val t = if written.nonEmpty && r.nextBoolean() then pick(written.toSeq*) else tuple()
            assertEquals(call("POST", s"/delete?tuple=${enc(TupleSyntax.show(t))}")._2, oracle.write(false, t).toString)
          case _ =>
            val (o, rel) = pick((doc, "viewer"), (doc, "editor"), (folder, "viewer"), (group, "member"))
            val p = user
            val at = Option.when(r.nextInt(3) == 0)(r.nextInt(oracle.latest + 1))
            val v = at.getOrElse(oracle.latest)
            val want = oracle.allowed(o, rel, p, v)
            val got = call("GET", s"/check?tuple=${enc(TupleSyntax.show(RelTuple(o, rel, Subject.Person(p))))}${at.fold("")(a => s"&at=$a")}")
            assertEquals(got, (200, if want then "yes" else "no", v.toString), (o, rel, p, v))
            checks += 1
      assert(checks > 150, checks)
    finally server.stop(0)
  }

  test("the server answers 500 and logs a broken contract, 503 a request over its time, and keeps serving others meanwhile") {
    val broken = new Backend:
      def schemaInForce = demoSchema
      def latest = 0
      def allowed(q: Query, v: Int) =
        if q.person == "slow" then { Thread.sleep(3000); true }
        else throw ContractViolation(Violation("CheckContract", "its check", List(q, v), Some(true)))
      def write(w: Write) = 1
    val err = java.io.ByteArrayOutputStream()
    val saved = System.err
    System.setErr(java.io.PrintStream(err, true))
    val server = RebacHttp.serve(0, broken, threads = 4, timeoutMs = 500)
    try
      val call = http(server)
      val (code, body, _) = call("GET", s"/check?tuple=${enc("doc:readme#viewer@user:ann")}")
      assertEquals(code, 500)
      assert(body.startsWith("internal error: CheckContract:"), body)
      assert(err.toString.contains("rebac: 500 for GET /check"), err.toString)
      val slow = scala.concurrent.Future(call("GET", s"/check?tuple=${enc("doc:readme#viewer@user:slow")}"))(using scala.concurrent.ExecutionContext.global)
      Thread.sleep(100)
      val t0 = System.nanoTime
      assertEquals(call("POST", s"/write?tuple=${enc("group:eng#member@user:ann")}")._1, 200)
      assert((System.nanoTime - t0) / 1000000 < 400, "a write waited behind a slow check")
      assertEquals(scala.concurrent.Await.result(slow, scala.concurrent.duration.Duration(10, "s"))._1, 503)
      // a query that is not URL-encoded text (the JDK client refuses to send one, so it goes over a socket)
      val socket = java.net.Socket("127.0.0.1", server.getAddress.getPort)
      try
        socket.getOutputStream.write("GET /check?tuple=%zz HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n".getBytes("UTF-8"))
        val status = scala.io.Source.fromInputStream(socket.getInputStream, "UTF-8").getLines().next()
        assert(status.contains(" 400 "), status)
      finally socket.close()
    finally
      server.stop(0)
      System.setErr(saved)
  }

  test("the server over HTTP: a write through a group and a folder, checks before and after, at a past version") {
    val server = RebacHttp.serve(0, RebacService(demoSchema, serviceLevels))
    try
      val call = http(server)
      val ann = enc("doc:readme#viewer@user:ann")
      val answers = List(
        call("POST", s"/write?tuple=${enc("folder:eng#viewer@group:eng#member")}"),
        call("POST", s"/write?tuple=${enc("doc:readme#parent@>folder:eng")}"),
        call("GET", s"/check?tuple=$ann"),
        call("POST", s"/write?tuple=${enc("group:eng#member@user:ann")}"),
        call("GET", s"/check?tuple=$ann"),
        call("POST", s"/delete?tuple=${enc("group:eng#member@user:ann")}"),
        call("GET", s"/check?tuple=$ann"),
        call("GET", s"/check?tuple=$ann&at=3"),
        call("POST", s"/write?tuple=${enc("doc:readme#viewer@group:eng#")}"))
      assertEquals(answers.map(_._1), List(200, 200, 200, 200, 200, 200, 200, 200, 400))
      assertEquals(answers.take(8).map(_._2), List("1", "2", "no", "3", "yes", "4", "no", "yes"))
      assertEquals(answers.take(8).map(_._3), List("1", "2", "2", "3", "3", "4", "4", "3"))
    finally server.stop(0)
  }
