package rebac

import frflow.*

/** How the service runs, owned as a design decision. */
val serviceWiring = Node.design("ServiceWiring",
  "One process holds the tuple store and the cache; a write is applied atomically and gets the next version; the HTTP layer answers checks with CachedChecks' flow at the version they name, from 0 to the latest; requests are parsed into tuples (a malformed one is refused with its reason), run on a pool of workers with a time limit each, and an internal error is answered 500 and logged, never a dropped connection.",
  why = "What a check answers is proven (CheckContract, CachedChecks), and how a request is answered is tested (HttpProtocol). What joins them, and keeps the cache sound from one request to the next, is decided here: the log only grows and a check never names a version past the latest, so the tuples of a version never change after it is written (Versions) and a kept answer stays the check's. That, the routes, parsing and the server's threads are reviewed, not proven.",
  idea = "Versions and the cache"
)("src/main/scala/rebac/Service.scala", "src/main/scala/rebac/Server.scala", "src/main/scala/rebac/TupleSyntax.scala").under(cachedChecks)

/** The vocabulary and the example data are owned with the nodes they serve. */
val domainFiles = Node.design("DomainFiles",
  "The domain's types and the code of the meaning (Domain.scala), and the data the examples are decided with (Demo.scala), are kept beside the nodes that use them.",
  why = "Every source file is governed by a node: a change to the types, to the code Derivation and Versions are written in, or to the example data is noticed.",
  idea = "Checks"
)("src/main/scala/rebac/Domain.scala", "src/main/scala/rebac/Demo.scala").under(checkContract)

val knowledge = KnowledgeBase("Rebac", idea = "IDEA.md")(
  checksExactly,
  versions,
  derivation,
  storeIndex,
  schemaIndex,
  checkContract,
  cacheKeepsAnswers,
  cachedChecks,
  httpProtocol,
  serviceWiring,
  domainFiles)
  .implementProven(checkContract)(resolveCheck, (q, v) => Resolution(tuplesOf.value, rulesFor.value).allowed(q, v, levels.value.size))
  .implementProven(storeIndex)(storedOf, (v, o) => TupleStore.of(writes.value).tuplesOf(v, o))
  .implementProven(schemaIndex)(rulesOf, SchemaIndex(schema.value).rulesFor)
  .implementProven(cachedChecks)(cachedCheck)
  // Names from a small vocabulary, so generated data meets itself: cycles of groups, relations the schema declares, a
  // kind and relation defined twice.
  .generating(vocabulary.objects.describedAs("objects of the kinds doc, folder, group, with ids a, b"))
  .generating(vocabulary.relationDefs.describedAs("relation definitions over the vocabulary's kinds and relations"))
  .generating(vocabulary.tuples.describedAs("tuples over the vocabulary: people ann and bob, usersets, links"))
  .generating(vocabulary.queries.describedAs("checks over the vocabulary"))
  .generating(vocabulary.requests.describedAs("requests as clients send them: mostly well formed, over the vocabulary"))
  .generating(vocabulary.served.describedAs("a schema over the vocabulary, a log, and the checks allowed at versions 0 to 6"))

/** The names generated data is drawn from. */
object vocabulary:
  private val kinds = Gen.oneOf("doc", "folder", "group")
  private val rels = Gen.oneOf("viewer", "editor", "member", "parent")
  private val people = Gen.oneOf("ann", "bob")
  val objects: Gen[Obj] = for k <- kinds; i <- Gen.oneOf("a", "b") yield Obj(k, i)
  private val rules: Gen[Rule] = Gen.choose(0, 2).flatMap {
    case 0 => Gen.const(Rule.Direct)
    case 1 => rels.map(Rule.Implied(_))
    case _ => for l <- rels; r <- rels yield Rule.Inherited(l, r)
  }
  val relationDefs: Gen[RelationDef] = for k <- kinds; r <- rels; rs <- Gen.listOf(rules) yield RelationDef(k, r, rs)
  private val subjects: Gen[Subject] = Gen.choose(0, 2).flatMap {
    case 0 => people.map(Subject.Person(_))
    case 1 => for o <- objects; r <- rels yield Subject.Members(o, r)
    case _ => objects.map(Subject.Link(_))
  }
  val tuples: Gen[RelTuple] = for o <- objects; r <- rels; s <- subjects yield RelTuple(o, r, s)
  val queries: Gen[Query] = for o <- objects; r <- rels; p <- people yield Query(o, r, p)

  // Requests as clients send them: mostly well formed, at the latest version or one near the log's length.
  private val ats: Gen[At] = Gen.choose(0, 3).flatMap {
    case 0 | 1 => Gen.const(At.Latest)
    case 2     => Gen.choose(-1, 6).map(At.Version(_))
    case _     => Gen.oneOf("x", "", "1.5").map(At.Invalid(_))
  }
  private val checked: Gen[RelTuple] = for q <- queries yield RelTuple(q.obj, q.rel, Subject.Person(q.person))
  val requests: Gen[Request] = Gen.choose(0, 9).flatMap {
    case 0 | 1 | 2 | 3 => for t <- checked; at <- ats yield Request.Check(Given.Tuple(t), at)
    case 4 | 5         => tuples.map(t => Request.Add(Given.Tuple(t)))
    case 6 | 7         => tuples.map(t => Request.Delete(Given.Tuple(t)))
    case 8             => ats.map(at => Request.Check(Given.Malformed("no subject"), at))
    case _             => Gen.oneOf(Request.Unknown("GET", "/"), Request.Unknown("PUT", "/write"), Request.Check(Given.Missing, At.Latest))
  }
  /** What the HTTP layer is tested over: a schema declaring some of the vocabulary's relations, a log, and the checks
    * the check allows, at versions near the log's length.
    */
  val served: Gen[Served] =
    for
      defs   <- Gen.listOf(relationDefs)
      log    <- Gen.listOf(tuples.flatMap(t => Gen.oneOf(Write.Add(t), Write.Remove(t))))
      allows <- Gen.listOf(for q <- queries; v <- Gen.choose(0, 6) yield Ask(q, v))
    yield Served(defs.distinctBy(d => (d.kind, d.rel)), log, allows)

object rebacCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/rebac", extensions = List(frflow.agent.Agent))
