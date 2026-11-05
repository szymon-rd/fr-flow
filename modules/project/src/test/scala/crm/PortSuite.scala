package crm

import cats.effect.IO
import cats.syntax.all.*
import frflow.*
import frflow.core.name.NodeId
import frflow.eval.{Running, Semantics}
import frflow.eval.flow.Wall
import frflow.eval.run.OnCode
import frflow.proof.audit.Completeness
import frflow.project.{Captured, Live, Ported, Projects}
import frflow.project.Ported.Lean
import frflow.project.program.ModelCheck
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.{ObligationStatus, ProverRun, Result}
import frflow.testing.model.{ModelRuns, ModelTests}
import frflow.testing.ported.Tested
import scala.concurrent.duration.*

/** Crm ported (owner §14, §21, §22, §40), against today's (`reference/crm`, ARCHITECTURE section 9, equivalence),
  * what it holds, its history and its clock the World's (owner §45 D): the database a model whose search is known only
  * by what is assumed of it (G2), the screens, the write side and the expiry job programs over it and the clock. Every
  * difference in where a node sits and what it assumes is listed and judged; checked by Lean and tested (the
  * database's SQLite and its in-memory variant against its model and what is assumed of its search, today's 1,000 runs
  * from seed 1 each), each node stands as today's but where judged, every consistency group proven (hand proofs,
  * owner §39); each claim as today stated it proven equivalent to the port's in every world meeting the database's
  * rules, or implying it, and section 9's seeded bugs in proven code refuted on a case (`resources/crm/port/Port.lean`;
  * the database's are `testing`'s `CrmSuite`); and today's examples hold on the code, those of runs run on SQLite.
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

  test("nothing is provided where the code runs: the history, what the CRM holds and the clock are the World's") {
    assertEquals(Ported.provided(elaborated), Set.empty[String])
    assertEquals(Ported.stoppedOnD(Judged.provided), Map.empty)
  }

  test("every difference from today's crm in where a node sits and what it assumes is listed and judged") {
    assertEquals(differences, Judged.differences.view.mapValues(_._1).toMap)
  }

  private val proofs = List("Lemmas", "readContract", "dealSearch", "searchesMatch", "visibility",
    "noCrossTenantRead", "writeContract", "saveWrite", "writesTakeEffect", "writesOnlyAsAsked", "recordsKept",
    "expiryJob", "crmRun", "keyedTables", "oneRowPerKey", "storeMirrorsRequests", "sharedCrm", "addedIsFound",
    "writesLeaveOthers", "Whole")
  private val lean = Lean(proofs.map(n => n -> Ported.proof("crm", "Crm", n)),
    reference.old("Crm", identity) :+ ("FrFlowGen/Port.lean" -> Ported.resource("crm/port/Port.lean")),
    Some("FrFlowGen.Port"))
  private val written = List(WriteExamples(), ExpireExamples())

  /** The database's Scala, SQLite and its in-memory variant, run against its model and what is assumed of its search,
    * today's 1,000 runs from seed 1 each; the clock's, the tests' wall clock, the model runs' default.
    */
  private def models: List[ModelCheck[IO]] =
    val semantics = Semantics(elaborated)
    val memory = t.vocabulary.model(databaseModel.name).toList.map { model =>
      val check = ModelTests.Check(model, ModelTests.of(databaseModel)(
        start = (tables: Tables) => MemoryDatabase.holding(tables),
        observe = (d: MemoryDatabase) => d.tables)(d => (d.load, d.storeAbout, d.logEvent, d.fetch)))
      ModelCheck(ModelRuns.reportedUnder(model.name), ModelRuns[IO](check, semantics, t, 1000).of(_, _))
    }
    ModelCheck.counted[IO](semantics, t, m => if m == databaseModel.name then 1000 else ModelRuns.Runs) ++ memory

  test(("checked by Lean and tested, each node stands as today's but where judged; consistent; the seeded proven " +
    "bugs refuted").tag(Live)) {
    val examples = written.flatMap(_.elaborated.fold(e => fail(e.toString), identity))
    Ported.run(elaborated, examples, lean, models).map { r =>
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
      // The examples, tried against the claims (owner §18): today's of a write shown; of the job's store, which
      // FrFlow's automation does not decide within an example's budget, proven by hand (`Whole.lean`).
      assertEquals(whole.collect { case Result(ObligationName.Example(i), s, _) => i -> s }.toMap,
        ((0 to 5).map(_ -> ObligationStatus.Shown) ++ (6 to 9).map(_ -> ObligationStatus.Proven)).toMap)
      r.port match
        case Some(ProverRun.Built(said)) => assert(!said.contains("sorryAx"), said)
        case other                       => fail(s"the seeded bugs are not refuted: $other")
    }
  }

  /** A run of the code as production runs it, on SQLite holding the tables, the clock at the time given. */
  private def on[A](from: (Tables, BigInt))(f: Running[IO] => IO[A]): IO[A] =
    for
      d   <- SqliteDatabase.holding(from._1)
      w   <- Wall.at[IO](from._2)
      run <- knowledge.running[IO](databaseModel := d, Clock.clockModel := w)
      a   <- f(run).guarantee(IO.blocking(d.db.close()))
    yield a

  /** Each example of a run: whether the run gives what it says, as it says. */
  private def held[I, O](xs: List[RunExample[I, O]])(f: (Running[IO], I) => IO[O]): IO[List[Boolean]] =
    xs.traverse(x => on(x.from)(f(_, x.inputs)).map(got => (got == x.gives) == x.holds))

  test("today's examples hold on the code: the database's search's, the screens', the write side's, the storing's") {
    for
      q  <- queries.traverse(x => SqliteDatabase.holding(x.from._1).flatMap(_.fetch(x.inputs._1, x.inputs._2))
              .map(got => (got == x.gives) == x.holds))
      r  <- held(reads)((run, q) => run(search)(q._1, q._2))
      d  <- held(dealRuns)((run, q) => run(dealsOf)(q._1, q._2))
      s  <- held(saves)((run, w) => run(saved)(w))
      st <- stores.traverse(x => SqliteDatabase.holding(x.from._1).flatMap(db =>
              db.storeAbout(x.inputs._1, x.inputs._2) *> db.tables.map(t => (t.store == x.gives) == x.holds)))
    yield assertEquals(List(q, r, d, s, st).map(v => v.count(identity) -> v.size), List(3 -> 3, 8 -> 8, 4 -> 4,
      3 -> 3, 3 -> 3))
  }

  test("today's examples of a write and of the expiry job's store hold on the code") {
    assertEquals(written.map(Tested.onCode), List(6, 4).map(List.fill(_)(OnCode.Holds)))
  }

  test("today's acmeNeverSeesGlobex and the root's expectation hold on the code") {
    val everything = Search.Everything
    import ExpectationsExamples.*
    for
      acme  <- on(acmeNeverSeesGlobex)(_(search)(Account("ann@acme", TenantId("acme")), everything))
      found <- expected.traverse((u, at, _) => on(tables -> at)(_(search)(u, everything)))
    yield
      assert(acme.nonEmpty && acme.forall(r => r.tenant != TenantId("globex") ||
        acmeNeverSeesGlobex._1.store.shares.contains(Share(r.id, TenantId("acme")))), acme)
      assertEquals(found, expected.map(_._3))
      assert(!found(2).contains(annContact))
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
      t   <- run(expireOnce)(now)
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
