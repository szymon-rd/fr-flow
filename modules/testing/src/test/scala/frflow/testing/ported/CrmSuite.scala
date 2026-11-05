package frflow.testing.ported

import cats.effect.{IO, Ref}
import cats.effect.unsafe.implicits.global
import crm.*
import frflow.core.name.{NodeId, SymbolName}
import frflow.eval.term.Semantics
import frflow.testing.derive.Derive
import frflow.testing.model.{ModelRuns, ModelTests}
import frflow.testing.{Plan, Settings}
import frflow.testing.report.{Failure, Outcome, TestReport}
import frflow.testing.steps.Difference

/** Crm's generated tests (today's `CrmSuite`): the database's Scala, SQLite and its in-memory variant, against its
  * model and what is assumed of its search, known only by assumptions (G2), on generated runs of its operations,
  * today's 1,000 from seed 1; the seeded SQL bugs and store bugs, each caught by a failing run.
  */
class CrmSuite extends munit.FunSuite:
  // A thousand generated runs a variant, the suites beside it running at once: on CI's two cores, minutes.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(5, "minutes")
  private val e = knowledge.elaborated.fold(es => fail(es.toString), identity)
  private val model = e.theory.vocabulary.model(databaseModel.name).getOrElse(fail("no database model"))

  private def runs[I](start: Tables => IO[I], observe: I => IO[Tables])(calls: I => Tuple): TestReport =
    val impl = ModelTests.of(databaseModel)(start, observe)(calls)
    ModelRuns[IO](ModelTests.Check(model, impl), Semantics(e), e.theory, 1000)
      .of(Plan(Settings.default, Nil), Derive.of(e, Nil)).unsafeRunSync()

  private def sqlite(select: Search => (String, List[Any])): TestReport =
    runs((t: Tables) => SqliteDatabase.searching(select)(t), (d: SqliteDatabase) => d.tables)(d =>
      (d.load, d.storeAbout, d.logEvent, d.fetch))

  private def memory(keepsShares: Boolean): TestReport =
    runs((t: Tables) => MemoryDatabase.holding(t, keepsShares), (d: MemoryDatabase) => d.tables)(d =>
      (d.load, d.storeAbout, d.logEvent, d.fetch))

  private def broke(r: TestReport): Option[(SymbolName, List[NodeId])] = r.outcome match
    case Outcome.Failed(Failure.Run(_, _, Difference.Assumed(s, _, broken), _)) => Some(s.op -> broken)
    case _                                                                      => None

  test("SQLite and the in-memory database keep the model and what is assumed of the search, 1,000 runs each") {
    List(sqlite(Db.selecting), memory(keepsShares = false)).foreach(r =>
      assertEquals((r.count.tried, r.outcome), (1000, Outcome.Passed)))
  }

  test("a seeded SQL bug (the search's WHERE dropped) breaks recordsByQuery on a generated run") {
    assertEquals(broke(sqlite(_ => ("", Nil))), Some(SymbolName("fetch") -> List(NodeId("recordsByQuery"))))
  }

  test("SQL that is right on the examples but drops rows on other searches breaks recordsByQuery on a generated run") {
    val limit2 = (q: Search) =>
      val (where, args) = Db.selecting(q)
      (s"where seq in (select seq from records $where order by seq limit 2)", args)
    assertEquals(broke(sqlite(limit2)), Some(SymbolName("fetch") -> List(NodeId("recordsByQuery"))))
  }

  test("an in-memory database keeping a record's old shares when it stores it again differs from the model, shrunk") {
    memory(keepsShares = true).outcome match
      case Outcome.Failed(Failure.Run(_, steps, Difference.State(_, _) | Difference.Call(_, _, _), _)) =>
        assert(steps.size <= 3, steps)
      case other => fail(other.toString)
  }

  test("a dropping database (its storing stores nothing) differs from the model on a generated run") {
    val dropping = runs((t: Tables) => SqliteDatabase.holding(t), (d: SqliteDatabase) => d.tables)(d =>
      (d.load, (_: BigInt, _: CrmStore) => IO.unit, d.logEvent, d.fetch))
    assert(dropping.outcome.isInstanceOf[Outcome.Failed], dropping.outcome)
  }

  /** The database in memory forgetting the other records' rows when it stores one. */
  private final class Forgetting(tables: Ref[IO, Tables]):
    def load: IO[CrmStore] = tables.get.map(_.store)
    def storeAbout(id: BigInt, s: CrmStore): IO[Unit] = tables.update(t => t.copy(store = CrmStore(
      s.records.filter(_.id == id), s.shares.filter(_.record == id), s.expiries.filter(_.record == id))))
    def logEvent(e: Event): IO[Unit] = tables.update(t => t.copy(events = t.events :+ e))
    def fetch(user: Account, q: Search): IO[List[CrmRecord]] =
      tables.get.flatMap(t => MemoryDatabase.holding(t).flatMap(_.fetch(user, q)))
    def held: IO[Tables] = tables.get

  test("a seeded bug in an in-memory database (the other records' rows forgotten) is found by generated runs") {
    val r = runs((t: Tables) => Ref[IO].of(t).map(Forgetting(_)), (m: Forgetting) => m.held)(m =>
      (m.load, m.storeAbout, m.logEvent, m.fetch))
    assert(r.failure.exists { case Failure.Run(_, steps, _, _) => steps.size <= 3
      case _ => false }, r.outcome)
  }
