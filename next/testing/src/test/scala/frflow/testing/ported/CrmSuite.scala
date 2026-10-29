package frflow.testing.ported

import cats.effect.{IO, Ref}
import cats.effect.unsafe.implicits.global
import crm.*
import frflow.*
import frflow.eval.Semantics
import frflow.eval.run.Broken
import frflow.testing.{Plan, Settings}
import frflow.testing.derive.Derive
import frflow.testing.model.{ModelRuns, ModelTests}
import frflow.testing.report.Failure

/** Crm's generated tests (today's `CrmSuite`, its testing cases' names kept): the database's plain Scala against its
  * assumptions' formulas, the seeded SQL and store bugs caught by generated cases, and an in-memory database run
  * against its model.
  */
class CrmSuite extends munit.FunSuite:
  // A thousand generated cases a claim, the suites beside it running at once: on CI's two cores, minutes, not 30 s.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(5, "minutes")
  private def with_(fetched: (CrmStore, Search) => List[CrmRecord], stored: (BigInt, CrmStore) => CrmStore) =
    FrModel("Crm")(knowledge.nodes*).copy(generators = knowledge.generators)
      .implementProvided(history, held, clock)
      .implementTested(fetch)(env => (_, q) => fetched(env(held), q))
      .implementTested(storeRows)(_ => stored)
      .implementProven(read)(search).implementProven(deals)(dealsOf).implementProven(write)(applyWrite)
      .implementProven(save)(saved).implementProven(expire)(expireCode).implementProven(runExpiry)(expireOnce)

  test("the database's plain code is tested against its assumptions: every generated case meets them") {
    assertEquals(Tested.nodes(knowledge).sorted, List("recordsByQuery", "storeEdits"))
    Tested.nodes(knowledge).foreach(n => assertEquals(Tested.passes(knowledge, n).count.tried, 1000, n))
  }

  private val sql = (store: CrmStore, q: Search) => Db.using(store)(_.recordsMatching(q))
  private val stores = (id: BigInt, t: CrmStore) => Db.using(CrmStore(Nil, Nil, Nil))(_.storeAbout(id, t))

  test("a seeded SQL bug (the search's WHERE dropped) is found by the generated cases") {
    val whereDropped = with_((store, q) => Db.using(store, _ => ("", Nil))(_.recordsMatching(q)), stores)
    assertEquals(Tested.failure(whereDropped, "recordsByQuery").broke, Broken.Post)
  }

  test("SQL that is right on the examples but drops rows on other inputs is found by the generated cases") {
    val limit2 = (q: Search) =>
      val (where, args) = Db.selecting(q)
      (s"where seq in (select seq from records $where order by seq limit 2)", args)
    val drops = with_((store, q) => Db.using(store, limit2)(_.recordsMatching(q)), stores)
    assertEquals(Tested.failure(drops, "recordsByQuery").broke, Broken.Post)
  }

  test("a seeded bug in an in-memory store (a record's old shares kept) is found by generated cases and shrunk") {
    val keeps = with_(sql, (id, t) =>
      CrmStore(t.records.filter(_.id == id), t.shares, t.expiries.filter(_.record == id)))
    val f = Tested.failure(keeps, "storeEdits")
    assertEquals(f.broke, Broken.Post)
    assert(f.toString.length < 400, f)
  }

  /** The database in memory: `keepsOthers` false forgets the other records' rows on a store. */
  private final class Memory(tables: Ref[IO, Tables], keepsOthers: Boolean):
    def load: IO[CrmStore] = tables.get.map(_.store)
    def storeAbout(id: BigInt, s: CrmStore): IO[Unit] = tables.update { t =>
      val others = if keepsOthers then t.store else CrmStore(Nil, Nil, Nil)
      t.copy(store = CrmStore(others.records.filterNot(_.id == id) ++ s.records.filter(_.id == id),
        others.shares.filterNot(_.record == id) ++ s.shares.filter(_.record == id),
        others.expiries.filterNot(_.record == id) ++ s.expiries.filter(_.record == id)))
    }
    def logEvent(e: Event): IO[Unit] = tables.update(t => t.copy(events = t.events :+ e))
    def held: IO[Tables] = tables.get

  private def modelRun(keepsOthers: Boolean) =
    val e = knowledge.elaborated.fold(es => fail(es.toString), identity)
    val memory = ModelTests.of(databaseModel)(start = (t: Tables) => Ref[IO].of(t).map(Memory(_, keepsOthers)),
      observe = (m: Memory) => m.held)(m => (m.load, m.storeAbout, m.logEvent))
    val model = e.theory.vocabulary.model(databaseModel.name).getOrElse(fail("no database model"))
    ModelRuns[IO](ModelTests.Check(model, memory), Semantics(e), e.theory)
      .of(Plan(Settings.default, Nil), Derive.of(e, Nil)).unsafeRunSync()

  test("the database's implementations are run against its model: the CRM's own in-memory store tested") {
    assertEquals(modelRun(keepsOthers = true).failure, None)
  }

  test("a seeded bug in an in-memory database (the other records' rows forgotten) is found by generated runs") {
    assert(modelRun(keepsOthers = false).failure.exists { case Failure.Run(_, steps, _, _) => steps.size <= 3
      case _ => false })
  }
