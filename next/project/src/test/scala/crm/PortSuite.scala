package crm

import cats.effect.IO
import frflow.*
import frflow.core.name.NodeId
import frflow.eval.Semantics
import frflow.eval.run.{Broken, OnCode}
import frflow.proof.audit.Completeness
import frflow.project.{Captured, Live, Ported, Projects, Tables as Sqlite}
import frflow.project.Ported.Lean
import frflow.project.program.ModelCheck
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.{ObligationStatus, ProverRun, Result}
import frflow.testing.{Plan, Settings}
import frflow.testing.derive.Derive
import frflow.testing.model.{ModelRuns, ModelTests}
import frflow.testing.ported.Tested
import frflow.testing.report.Outcome
import scala.concurrent.duration.*

/** Crm ported (owner §14, §21, §22, §40), against today's (`reference/crm`, ARCHITECTURE section 9, equivalence):
  * every difference in where a node sits and what it assumes is listed and judged; checked by Lean and tested
  * (1,000 cases from seed 1), the database's SQLite and its in-memory variant run against its model; each node
  * stands as today's but where judged, every consistency group proven; section 9's seeded bugs are caught,
  * the proven code's by Lean refuting what it would claim on a case (`resources/crm/port/Port.lean`); and today's
  * examples hold on the code.
  */
class PortSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes
  private val reference = Captured("crm")
  private val elaborated = Projects.elaborated(knowledge)
  private val t = elaborated.theory

  private def differences: Map[String, String] =
    val now = t.nodes.map(_.node.id.value)
    val gone = reference.nodes.filterNot(now.contains).map(_ -> "gone")
    val added = now.filterNot(reference.nodes.contains).map(_ -> "new")
    val moved = now.filter(reference.nodes.contains).flatMap { n =>
      val id = NodeId(n)
      val parts = t.refinement.parts(id).map(_.value)
      val newParts = parts.filterNot(reference.parts(n).contains)
      val lost = reference.parts(n).filter(now.contains).filterNot(parts.contains)
      val assumes = t.refinement.assumed(id).map(_.value)
      val (more, less) = (assumes.filterNot(reference.assumes(n).contains),
        reference.assumes(n).filterNot(assumes.contains))
      List(Option.when(newParts.nonEmpty)(s"${newParts.mkString(", ")} ${if newParts.size == 1 then "is a part"
        else "are parts"}"),
        Option.when(lost.nonEmpty)(s"${lost.mkString(", ")} no part"),
        Option.when(more.nonEmpty || less.nonEmpty)("assumes " + (more.map("+" + _) ++ less.map("-" + _))
          .mkString(" "))).flatten.map(d => n -> d)
    }
    (gone ++ added ++ moved).groupMapReduce(_._1)(_._2)(_ + "; " + _)

  test("every difference from today's crm in where a node sits and what it assumes is listed and judged") {
    assertEquals(differences, Judged.differences.view.mapValues(_._1).toMap)
  }

  private val proofs = List("Lemmas", "writeContract", "saveWrite", "writesTakeEffect", "writesOnlyAsAsked",
    "recordsKept", "visibility", "storeMirrorsRequests", "sharedCrm", "addedIsFound", "writesLeaveOthers",
    "expiryJob", "keyedTables",
    "oneRowPerKey", "Whole")
  private val lean = Lean(proofs.map(n => n -> Ported.resource(s"crm/proofs/$n.lean")),
    reference.old("Crm", identity) :+ ("FrFlowGen/Port.lean" -> Ported.resource("crm/port/Port.lean")),
    Some("FrFlowGen.Port"))
  private val written = List(ExpectationsExamples(), QueryExamples(), ReadExamples(), DealExamples(),
    WriteExamples(), SaveExamples(), StoreExamples(), ExpireExamples())

  /** The database's in-memory variant, run against its model as SQLite is; `keepsShares`, the seeded bug. */
  private def memory(keepsShares: Boolean): List[ModelCheck[IO]] =
    t.vocabulary.model(databaseModel.name).toList.map { model =>
      val check = ModelTests.Check(model, ModelTests.of(databaseModel)(
        start = (tables: Tables) => MemoryDatabase.holding(tables, keepsShares),
        observe = (d: MemoryDatabase) => d.tables)(d => (d.load, d.storeAbout, d.logEvent)))
      ModelCheck(ModelRuns.reportedUnder(model.name), ModelRuns[IO](check, Semantics(elaborated), t).of(_, _))
    }

  test(("checked by Lean and tested, each node stands as today's but where judged; consistent; the seeded proven " +
    "bugs refuted").tag(Live)) {
    val examples = written.flatMap(_.elaborated.fold(e => fail(e.toString), identity))
    Ported.run(elaborated, examples, lean, Sqlite.sqlite(elaborated) ++ memory(false)).map { r =>
      val a = r.analysis
      assertEquals(Completeness.of(a.decided, a.modules), Nil)
      val now = t.nodes.map(_.node.id).map(id => id.value.capitalize -> Ported.row(a, id)).toMap
      val compared = (reference.standings.keys ++ now.keys).toList.distinct.sorted
        .filter(k => now.get(k) != reference.standings.get(k)).map(k => k -> now.getOrElse(k, Nil))
      assertEquals(compared.toMap, Judged.standings, s"crm now:\n${Ported.table(a)}")
      assertEquals(Ported.unproven(a), Judged.stopped)
      val whole = a.wholeCheck.map(_.results).getOrElse(fail("the theory's own check is not recorded"))
      assertEquals(whole.collect { case Result(n @ ObligationName.Consistent(_), s, _) => n -> s }.toMap,
        a.groups.map((i, _) => ObligationName.Consistent(i) -> ObligationStatus.Proven).toMap)
      // The examples giving no value, tried against the claims (owner §18): the purpose's, proven by hand
      // (`Whole.lean`); the write's, the store's and the job's shown; the write side's not: given what storeEdits
      // says of the rows the code leaves open, FrFlow's automation does not decide them within an example's budget
      // (`ExampleGoals.Heartbeats`; today's Lean evaluated the code).
      val shown = (17 to 22) ++ (26 to 32)
      assertEquals(whole.collect { case Result(ObligationName.Example(i), s, _) => i -> s }.toMap,
        Map(0 -> ObligationStatus.Proven) ++ shown.map(_ -> ObligationStatus.Shown) ++
          (23 to 25).map(_ -> ObligationStatus.NotShown))
      r.port match
        case Some(ProverRun.Built(said)) => assert(!said.contains("sorryAx"), said)
        case other                       => fail(s"the seeded bugs are not refuted: $other")
    }
  }

  /** Crm with the database's search and store given other code. */
  private def with_(fetched: (CrmStore, Search) => List[CrmRecord],
      stored: (BigInt, CrmStore) => CrmStore = (id, s) => Db.using(CrmStore(Nil, Nil, Nil))(_.storeAbout(id, s)))
      : FrModel =
    FrModel("Crm")(knowledge.nodes*).copy(generators = knowledge.generators)
      .implementProvided(history, held, clock)
      .implementTested(fetch)(env => (_, q) => fetched(env(held), q))
      .implementTested(storeRows)(_ => stored)
      .implementProven(read)(search).implementProven(deals)(dealsOf).implementProven(write)(applyWrite)
      .implementProven(save)(saved).implementProven(expire)(expireCode).implementProven(runExpiry)(expireOnce)

  test("SQL WHERE dropped: a search returning every stored record fails a generated case of recordsByQuery") {
    val all = with_((store, q) => Db.using(store, _ => ("", Nil))(_.recordsMatching(q)))
    assertEquals(Tested.failure(all, "recordsByQuery").broke, Broken.Post)
  }

  test("SQL with LIMIT 2: right on the examples, it fails a generated case of recordsByQuery") {
    val limit2 = (q: Search) =>
      val (where, args) = Db.selecting(q)
      (s"where seq in (select seq from records $where order by seq limit 2)", args)
    assertEquals(Tested.onCode(QueryExamples()), List.fill(3)(OnCode.Holds))
    val dropping = with_((store, q) => Db.using(store, limit2)(_.recordsMatching(q)))
    assertEquals(Tested.failure(dropping, "recordsByQuery").broke, Broken.Post)
  }

  test("dropping database: a store that stores nothing fails a generated case of storeEdits") {
    val nothing = with_((store, q) => Db.using(store)(_.recordsMatching(q)), (_, _) => CrmStore(Nil, Nil, Nil))
    assertEquals(Tested.failure(nothing, "storeEdits").broke, Broken.Post)
  }

  test("an in-memory store that keeps a record's old shares is found by generated runs against the model") {
    val run = memory(keepsShares = true).head.run(Plan(Settings.default, Nil), Derive.of(elaborated, Nil))
    run.map(r => assert(r.outcome.isInstanceOf[Outcome.Failed], r.outcome))
  }

  test("today's examples hold on the code: the database's, the screens', the write side's and the job's") {
    assertEquals(written.tail.map(Tested.onCode), List(3, 9, 4, 6, 3, 3, 4).map(List.fill(_)(OnCode.Holds)))
  }

  /** Today's examples of the expiry job, each a run on SQLite from the tables given: the store it returns, and the
    * tables after, or what they are never.
    */
  private val acmeDeal = CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")
  private val acmeContact = CrmRecord(2, TenantId("acme"), Kind.Contact, "Acme contact")
  private val globexUntil100 = CrmStore(List(acmeDeal), List(Share(1, TenantId("globex")),
    Share(1, TenantId("initech"))), List(Expiry(1, TenantId("globex"), 100)))
  private val initechOnly = CrmStore(List(acmeDeal), List(Share(1, TenantId("initech"))), Nil)
  private val twoUnsorted = CrmStore(List(acmeContact, acmeDeal), List(Share(2, TenantId("globex")),
    Share(1, TenantId("initech"))), List(Expiry(2, TenantId("globex"), 100)))
  private val earlier = List(Event.Wrote(WriteCmd(Account("ann@acme", TenantId("acme")), Change.Add(acmeDeal))))

  private def job(now: BigInt, from: CrmStore): IO[(CrmStore, Tables)] =
    for
      d   <- SqliteDatabase.holding(Tables(from, earlier))
      run <- knowledge.running[IO](databaseModel := d)
      t   <- ExpireOnce.run[IO](run.term(now))(using run).map(run.value)
      after <- d.tables
      _   <- IO.blocking(d.db.close())
    yield (t, after)

  test("today's examples of the expiry job hold on SQLite: what ended is dropped, rows stored again, the run logged") {
    for
      ended  <- job(150, globexUntil100)
      two    <- job(150, twoUnsorted)
      before <- job(50, globexUntil100)
    yield
      assertEquals(ended, (initechOnly, Tables(initechOnly, earlier :+ Event.Expired(150))))
      assertEquals(two, (CrmStore(List(acmeContact, acmeDeal), List(Share(1, TenantId("initech"))), Nil),
        Tables(CrmStore(List(acmeDeal, acmeContact), List(Share(1, TenantId("initech"))), Nil),
          earlier :+ Event.Expired(150))))
      assertEquals(before, (globexUntil100, Tables(globexUntil100, earlier :+ Event.Expired(50))))
      // A run that stores nothing leaves an ended share in the database; one is never left out of the log.
      assertNotEquals(ended._2, Tables(globexUntil100, earlier :+ Event.Expired(150)))
      assertNotEquals(ended._2, Tables(initechOnly, earlier))
  }

  test("the code is tested with today's seed and cases: the database's search and store, 1,000 cases from seed 1") {
    assertEquals(Tested.nodes(knowledge).map(n => n -> Tested.passes(knowledge, n, written).seed.value).toMap,
      Map("recordsByQuery" -> 1L, "storeEdits" -> 1L))
  }
