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

  test("the store's and the schema's indexes are checked against their promises on generated data") {
    for n <- List(storeIndex, schemaIndex) do
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
    assertEquals(s.check(ann, Some(3)), true)
    demoWrites.drop(3).foreach(s.write)
    assertEquals(List(1, 2, 3, 4, 5).map(v => s.check(ann, Some(v))), List(false, false, true, true, false))
    assertEquals(s.check(ann, Some(99)), false) // never past the latest: version 5
    assertEquals(s.check(Query(readme, "viewer", "bob"), None), true)
    assertEquals(s.check(Query(readme, "editor", "ann"), Some(3)), false)
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

  test("the server over HTTP: a write through a group and a folder, checks before and after, at a past version") {
    val server = RebacHttp.serve(0, RebacService(demoSchema, serviceLevels))
    try
      val http = java.net.http.HttpClient.newHttpClient()
      def call(m: String, path: String) =
        val req = java.net.http.HttpRequest.newBuilder(java.net.URI.create(s"http://127.0.0.1:${server.getAddress.getPort}$path"))
          .method(m, java.net.http.HttpRequest.BodyPublishers.noBody()).build()
        val res = http.send(req, java.net.http.HttpResponse.BodyHandlers.ofString())
        (res.statusCode, res.body.trim)
      def enc(t: String) = java.net.URLEncoder.encode(t, "UTF-8")
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
    finally server.stop(0)
  }

  test("the HTTP layer: checks and writes, and refusals with the reason") {
    val s = RebacService(demoSchema, serviceLevels)
    def call(m: String, path: String, tuple: String, at: Option[Int] = None) =
      RebacHttp.answer(s, m, path, Map("tuple" -> tuple) ++ at.map(v => "at" -> v.toString))
    assertEquals(call("POST", "/write", "folder:eng#viewer@group:eng#member"), (200, "1"))
    assertEquals(call("POST", "/write", "doc:readme#parent@>folder:eng"), (200, "2"))
    assertEquals(call("GET", "/check", "doc:readme#viewer@user:ann"), (200, "no"))
    assertEquals(call("POST", "/write", "group:eng#member@user:ann"), (200, "3"))
    assertEquals(call("GET", "/check", "doc:readme#viewer@user:ann"), (200, "yes"))
    assertEquals(call("GET", "/check", "doc:readme#viewer@user:ann", Some(2)), (200, "no"))
    assertEquals(call("GET", "/check", "doc:readme#viewer@group:eng#member")._1, 400)
    assertEquals(call("POST", "/write", "doc:readme#viewer@group:eng#")._1, 400)
  }
