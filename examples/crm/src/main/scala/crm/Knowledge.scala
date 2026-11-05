package crm

import cats.effect.IO
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

/** The tables as the CRM's history leaves them: some events, each saved or run in turn from the empty tables. */
private val tablesAsRun = Gens.derived[List[Event]].map(History.tables).describedAs("tables as their history left them")

/** The FrModel's code, apart from its nodes: a variant keeps all but one. */
def withCode(kb: FrModel): FrModel = kb
  .implementTested(load, storeAbout, logEvent, fetch)(start = SqliteDatabase.holding, observe = _.tables)(d =>
    (d.load, d.storeAbout, d.logEvent, d.fetch))
  .implementTested(Clock.now, Clock.sleep, Clock.elapse)(start = Wall.at[IO], observe = _.time)(c =>
      (c.now, c.sleep, c.elapse))
  .implementProven(read)(search)
  .implementProven(deals)(dealsOf)
  .implementProven(write)(applyWrite)
  .implementProven(save)(saved)
  .implementProven(expire)(expireCode)
  .implementProven(runExpiry)(expireOnce)
  .withGenerator(tableStores)
  .withGenerator(tablesAsRun)

val knowledge = withCode(FrModel("Crm")(sharedCrm, addedIsFound, writesLeaveOthers, companies, ownership, searches,
  searchesAsk, adding, sharing, crmRun, storeMirrorsRequests, visibility, noCrossTenantRead, searchesMatch,
  recordsByQuery, searchKeeps, readContract, dealSearch, readSideWiring, writesTakeEffect, writesOnlyAsAsked,
  recordsKept, writeContract, saveWrite, writeSideWiring, sharesExpire, tablesModel, runsOneAtATime,
  expiryJob, expiryJobWiring, keyedTables, tablesStartEmpty, oneRowPerKey, httpApi))
