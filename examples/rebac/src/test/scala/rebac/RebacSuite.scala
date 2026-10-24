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

  test("the model is well formed: one root split into its safety and capability halves, the check's contract under both") {
    assertEquals(knowledge.problems, Nil)
    assertEquals(knowledge.root.map(_.id), Some("ChecksExactly"))
    assertEquals(knowledge.parts(checksExactly).map(_.id), List("OnlyGivenAccess", "GivenAccessAnswered"))
    assertEquals(knowledge.parentsOf(checkContract).map(_.id), List("OnlyGivenAccess", "GivenAccessAnswered"))
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

  test("the service: writes get versions, and a check answers by the tuples of its version, through the cache") {
    val s = RebacService(demoSchema, serviceLevels)
    demoWrites.foreach(s.write)
    val ann = Query(readme, "viewer", "ann")
    assertEquals(List(1, 2, 3, 4, 5).map(v => s.check(ann, Some(v))), List(false, false, true, true, false))
    assertEquals(s.check(ann, Some(3)), true) // again: from the cache, the same answer
    assertEquals(s.check(Query(readme, "viewer", "bob"), None), true)
    assertEquals(s.check(Query(readme, "editor", "ann"), Some(3)), false)
  }

  test("tuple strings: users, usersets and links parse; anything else is refused") {
    assertEquals(RebacService.parse("doc:readme#viewer@user:ann"), Some(RelTuple(readme, "viewer", Subject.Person("ann"))))
    assertEquals(RebacService.parse("folder:eng#viewer@group:eng#member"), Some(RelTuple(eng, "viewer", Subject.Members(engGroup, "member"))))
    assertEquals(RebacService.parse("doc:readme#parent@>folder:eng"), Some(RelTuple(readme, "parent", Subject.Link(eng))))
    for bad <- List("", "doc:readme", "doc:readme#viewer", "doc#viewer@user:ann", "doc:readme#viewer@ann", "doc:readme#@user:ann") do
      assertEquals(RebacService.parse(bad), None, bad)
  }
