package crm

import cats.syntax.all.*
import frflow.*

val httpApi = Node.design("The HTTP API answers searches through the records screen and the sales screen, and " +
    "writes through the write side; who calls is the account in the request's headers.")(
  "src/main/scala/crm/Server.scala")
  .refines(sharedCrm)

/** A store as its tables hold it: one row per key (a record by its id, a share and an expiry by record and company). */
private val tableStores = (for
  rs <- Gens.derived[List[CrmRecord]]; ss <- Gens.derived[List[Share]]; es <- Gens.derived[List[Expiry]]
yield CrmStore(rs.distinctBy(_.id), ss.distinctBy(s => (s.record, s.to)), es.distinctBy(e => (e.record, e.to))))
  .describedAs("stores with one row per key, as the tables hold them")

val knowledge = FrModel("Crm")(sharedCrm, addedIsFound, writesLeaveOthers, companies, ownership, searches,
  searchesAsk, adding, sharing, crmRun, storeMirrorsRequests, visibility, noCrossTenantRead, searchesMatch,
  recordsByQuery, acmeNeverSeesGlobex, readContract, dealSearch, readSideWiring, writesTakeEffect, writesOnlyAsAsked,
  recordsKept, writeContract, saveWrite, storeEdits, writeSideWiring, sharesExpire, tablesModel, runsOneAtATime,
  expiryJob, expiryJobWiring, httpApi)
  .implementProvided(history, held, clock)
  .implementTested(fetch)(env => (_, q) => InMemory.recordsMatching(env(held), q))
  .implementTested(storeRows)(_ => (id, t) => InMemory.storeAbout(id, t))
  .implementProven(read)(search)
  .implementProven(deals)(dealsOf)
  .implementProven(write)(applyWrite)
  .implementProven(save)(saved)
  .implementProven(expire)(expireCode)
  .implementProven(runExpiry)(expireOnce)
  .generating(tableStores)
