package auth

import frflow.*
import java.nio.file.{Files, Paths}

class AuthSuite extends munit.FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

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

  test("the knowledge base is proven, from the root to the contract") {
    val lake = Lake(Paths.get("."))
    assume(lake.available, "lake is not available")
    val root = Files.createTempDirectory("auth")
    Files.copy(Paths.get("examples/auth/IDEA.md"), root.resolve("IDEA.md"))
    val w = Workflow(knowledge, Workspace(root, Paths.get("lean").toAbsolutePath.toString))
    assertEquals(w.check().map((n, c) => n.id -> c.status),
      List("NoUnauthorizedAccess" -> "proven", "Authenticated" -> "proven", "GrantBased" -> "proven", "DecisionContract" -> "proven"))
    assert(w.context(decisionContract).contains("No user may ever"))
  }
