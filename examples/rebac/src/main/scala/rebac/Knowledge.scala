package rebac

import frflow.*

/** How the service runs, owned as a design decision. */
val serviceWiring = Node.design("ServiceWiring",
  "One process holds the tuple store and the cache; a write is applied atomically and gets the next version; a check runs CachedChecks' flow at the version it names, never past the latest, through the cache; requests are parsed into tuples, and a malformed one is refused with its reason.",
  why = "What a check answers is proven (CheckContract, CachedChecks). What keeps the cache sound from one request to the next is decided here: the log only grows and a check never names a version past the latest, so the tuples of a version never change after it is written (Versions) and a kept answer stays the check's. That, and parsing, are reviewed, not proven.",
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
  serviceWiring,
  domainFiles)
  .implementProven(checkContract)(resolveCheck)
  .implementProven(storeIndex)(storedOf, (v, o) => TupleStore.of(writes.value).tuplesOf(v, o))
  .implementProven(schemaIndex)(rulesOf, SchemaIndex(schema.value).rulesFor)
  .implementProven(cachedChecks)(cachedCheck)

object rebacCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/rebac", extensions = List(frflow.agent.Agent))
