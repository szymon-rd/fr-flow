package frflow.testing.ported

import cats.effect.IO
import cats.effect.unsafe.implicits.global
import frflow.core.name.{NodeId, SymbolName}
import frflow.eval.Semantics
import frflow.testing.{Plan, Settings}
import frflow.testing.derive.Derive
import frflow.testing.model.{Difference, ModelRuns, ModelTests}
import frflow.testing.report.{Failure, Outcome}
import keycloak.*

/** Keycloak's generated tests (today's `KeycloakSuite`): the store's Scala against what is assumed of its operations
  * known only by assumptions (G2), on generated runs of its operations, today's 1,000 from seed 1; and section 9's two
  * seeded bugs of the store, each caught by a failing run. The introspection is proven code now: its seeded bug is
  * refuted in Lean (`project`'s `PortSuite`).
  */
class KeycloakSuite extends munit.FunSuite:
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(5, "minutes")
  private val e = knowledge.elaborated.fold(es => fail(es.toString), identity)
  private val model = e.theory.vocabulary.model(serverStore.name).getOrElse(fail("no store"))

  private def runs(calls: SessionDb => Tuple): frflow.testing.report.TestReport =
    val impl = ModelTests.of(serverStore)(start = SessionDb.holding, observe = (d: SessionDb) => d.stored)(calls)
    ModelRuns[IO](ModelTests.Check(model, impl), Semantics(e), e.theory, 1000)
      .of(Plan(Settings.default, Nil), Derive.of(e, Nil)).unsafeRunSync()

  private def broke(r: frflow.testing.report.TestReport): Option[(SymbolName, List[NodeId])] = r.outcome match
    case Outcome.Failed(Failure.Run(_, _, Difference.Assumed(s, _, broken), _)) => Some(s.op -> broken)
    case _                                                                      => None

  test("the store's Scala keeps what is assumed of storing a request and looking a token up, 1,000 runs") {
    val r = runs(d => (d.load, d.record, d.lookup))
    assertEquals((r.count.tried, r.outcome), (1000, Outcome.Passed))
  }

  test("a store that drops the sessions it is given breaks storeKeepsState and storeLogs on a generated run") {
    val dropping = runs(d => (d.load, (q: AuthRequest, after: ServerState) =>
      d.record(q, after.copy(sessions = Nil)), d.lookup))
    assertEquals(broke(dropping).map(_._1), Some(SymbolName("record")))
    assert(broke(dropping).exists(_._2.contains(NodeId("storeKeepsState"))), dropping)
  }

  test("an index answering with another realm's session breaks sessionLookup on a generated run") {
    val leaky = runs(d => (d.load, d.record, (_: RealmId, token: String) =>
      IO.pure(Option(Session(token, globex, "carol")))))
    assertEquals(broke(leaky), Some(SymbolName("lookup") -> List(NodeId("sessionLookup"))))
  }
