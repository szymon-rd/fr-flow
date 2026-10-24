package rebac

import frflow.*

/** How the service runs, owned as a design decision. */
val serviceWiring = Node.design("ServiceWiring",
  "One process holds the tuple store and the cache; a write is applied under a lock and gets the next version; a check runs CachedChecks' flow at the version it names, or the latest, through the cache.",
  why = "What a check answers is proven (CheckContract, CachedChecks); that writes are serialised, that a check reads one version, and how requests are parsed are decided here and reviewed. Tuple strings are parsed by plain code (RebacService.parse): a malformed one is refused with a 400, so it can never become a tuple.",
  idea = "Versions and the cache"
)("src/main/scala/rebac/Server.scala").under(cachedChecks)

/** The vocabulary, the example data and the stores are owned with the nodes they serve. */
val domainFiles = Node.design("DomainFiles",
  "The domain's types and the meaning of a derivation (Domain.scala), and the data the examples are decided with (Demo.scala), are kept beside the nodes that use them.",
  why = "Every source file is governed by a node: a change to the vocabulary or to the example data is noticed on the root.",
  idea = "Checks"
)("src/main/scala/rebac/Domain.scala", "src/main/scala/rebac/Demo.scala").under(checkContract)

val knowledge = KnowledgeBase("Rebac", idea = "IDEA.md")(
  checksExactly,
  onlyGivenAccess,
  givenAccessAnswered,
  checkContract,
  storeIndex,
  schemaIndex,
  cacheKeepsAnswers,
  cachedChecks,
  serviceWiring,
  domainFiles)
  .implementProven(checkContract)(resolveCheck)
  .implementProven(storeIndex)(storedOf, TupleStore.replaying(writes.value).tuplesOf)
  .implementProven(schemaIndex)(rulesOf, SchemaIndex(schema.value).rulesFor)
  .implementProven(cachedChecks)(cachedCheck)

object rebacCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/rebac", extensions = List(frflow.agent.Agent))
