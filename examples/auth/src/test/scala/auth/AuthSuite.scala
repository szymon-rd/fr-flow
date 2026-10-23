package auth

import frflow.*
import cats.effect.IO
import frflow.api.{FrFlowError, LiveApi}
import frflow.check.Workspace
import java.nio.file.{Files, Paths}

class AuthSuite extends munit.CatsEffectSuite:
  // The API over the example's own workspace; nothing here decides, so no key is read.
  private def api = LiveApi(knowledge, Workspace(Paths.get("examples/auth").toAbsolutePath.normalize, "../../../lean"), Paths.get("no.key"), Map.empty)
  private def checked = api.flatMap(_.check(None)).recoverWith { case FrFlowError.LeanMissing => IO(assume(false, "lake is not available")) *> IO.never }

  test("the committed ledger accepts every node: none is up for review, none is gone") {
    // As `auth/run status` reads it: a change to the content, the hashes or the code fingerprints shows here.
    api.flatMap(_.view).map { v =>
      val annotated = v.annotated
      val states = annotated.nodes.map(r => r.id.value -> r.state.toString)
      assertEquals(states.size, knowledge.nodes.size)
      assertEquals(states.filter(_._2 != "accepted"), Nil)
      assertEquals(annotated.gone, Nil)
    }
  }

  override val munitIOTimeout = scala.concurrent.duration.Duration(20, "min")

  private val alice = UserId("alice")
  private val report = Path("/reports/q3")
  private val grantTable = List(Grant(alice, report))
  private val tokens = Map("t-1" -> alice)

  test("the service grants exactly what the grant table allows") {
    val decide = service(grantTable, tokens)
    assertEquals(decide("t-1", report), Some(alice))
    assertEquals(decide("t-1", Path("/admin")), None)
    assertEquals(decide("forged", report), None)
  }

  test("an implementation that ignores the grant table is stopped by its contract") {
    val careless: (String, Path) => Option[UserId] = (t, _) => tokens.get(t)
    val decide = knowledge.implement(decisionContract)(careless).service(decisionContract)(grants.bind(grantTable), sessions.bind(t => tokens.get(t)))
    assertEquals(decide("t-1", report), Some(alice))
    intercept[ContractViolation](decide("t-1", Path("/admin")))
  }

  test("the examples pass against the contract and the implementation") {
    assert(knowledge.exampleResults(decisionContract).forall(r => r.contract == "ok" && r.implementation.contains("ok")),
      knowledge.exampleResults(decisionContract))
  }

  test("the model is well formed: one root, its parts, the definitions of the domain, the contract under all three parts") {
    assertEquals(knowledge.problems, Nil)
    assertEquals(knowledge.root.map(_.id), Some("AccessExactly"))
    assertEquals(knowledge.parentsOf(decisionContract).map(_.id), List("TokenNamesHolder", "AccessNeedsGrant", "GrantLetsIn"))
  }

  test("the knowledge base is proven, from the contract and its code to the root") {
    // In the example's own workspace, as `auth/run check` checks it: its Lean build and recorded results
    // are reused while current.
    for
      report <- checked
      details <- api.flatMap(_.details(frflow.protocol.NodeId(decisionContract.id)))
    yield
      assertEquals(report.nodes.map(c => c.id.value -> c.status.toString),
        List("AccessExactly" -> "proven", "TokenNamesHolder" -> "proven", "AccessNeedsGrant" -> "proven", "GrantLetsIn" -> "proven", "DecisionContract" -> "proven"))
      assertEquals(report.view.snapshot.root.flatMap(report.view.node).flatMap(_.node.rootImpl).map(_.status.toString), Some("proven"))
      assertEquals(report.view.snapshot.trusted, Nil)
      assert(details.idea.contains("No user may ever"), details.idea)
  }
