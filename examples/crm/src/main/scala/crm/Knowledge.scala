package crm

import frflow.*

/** The HTTP API, owned as a design decision: every request goes through the screens and the write side. */
val httpApi = Node.design(
  "HttpApi",
  "The HTTP API answers searches through the records screen and the sales screen, and writes through the write side; who calls is the account in the request's headers.",
  why = "Every request must reach the records only through service. Authentication is not modelled: the headers name the account."
)("src/main/scala/crm/Server.scala")
  .under(sharedCrm)
  .exempt(noCrossTenantRead, "it returns only what the records screen and the sales screen return, which keep the rule")

val knowledge = KnowledgeBase("Crm", idea = "IDEA.md")(
  sharedCrm, addedAreFound,
  companies, searches, crmRun, liveShares, adding,
  visibility, noCrossTenantRead, searchesMatch, readContract, dealSearch, recordsByQuery, readSideWiring,
  writesTakeEffect, writesInCompany, storeConsistent, recordsKept, writeContract, saveWrite, storeEdits, writeSideWiring,
  sharesExpire, expiryJobWiring,
  httpApi)
  .implementProven(recordsByQuery)(storedMatching, (u, q) => database.value.recordsMatching(q))
  .implementProven(storeEdits)(storedAbout, (id, t) => database.value.storeAbout(id, t))
  .implementProven(readContract)(search)
  .implementProven(dealSearch)(dealsOf)
  .implementProven(writeContract)(applyWrite)
  .implementProven(saveWrite)(saved)
  .implementProven(sharesExpire)(expireCode)

@main def crmCli(args: String*): Unit = sys.exit(knowledge.cli(args, root = "examples/crm"))
