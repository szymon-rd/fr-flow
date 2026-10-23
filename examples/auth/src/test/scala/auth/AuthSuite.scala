package auth

import frflow.*
import cats.effect.unsafe.implicits.global
import frflow.check.*
import java.nio.file.{Files, Paths}

class AuthSuite extends munit.FunSuite:

  test("the committed ledger accepts every node: none is up for review, none is gone") {
    // As `auth/run status` reads it: a change to the content, the hashes or the code fingerprints shows here.
    val annotated = Workflow(knowledge, Workspace(Paths.get("examples/auth").toAbsolutePath.normalize, "../../../lean"))
      .flatMap(_.analysis).unsafeRunSync().annotated
    val states = annotated.nodes.map(r => r.id.value -> r.state.toString)
    assertEquals(states.size, knowledge.nodes.size)
    assertEquals(states.filter(_._2 != "accepted"), Nil)
    assertEquals(annotated.gone, Nil)
  }

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

  test("the model is well formed: one root, its parts, the definitions of the domain, the contract under all three parts") {
    assertEquals(knowledge.problems, Nil)
    assertEquals(knowledge.root.map(_.id), Some("AccessExactly"))
    assertEquals(knowledge.parentsOf(decisionContract).map(_.id), List("TokenNamesHolder", "AccessNeedsGrant", "GrantLetsIn"))
  }

  test("the knowledge base is proven, from the contract and its code to the root") {
    assume(Config.load.flatMap(Lake(Paths.get("."), _)).flatMap(_.available).unsafeRunSync(), "lake is not available")
    // In the example's own workspace, as `auth/run check` checks it: its Lean build and recorded results
    // are reused while current.
    val w = Workflow(knowledge, Workspace(Paths.get("examples/auth").toAbsolutePath.normalize, "../../../lean"))
    val checked = w.flatMap(_.check()).unsafeRunSync()
    val r = checked.results
    assertEquals(r.map((n, c) => n.id -> c.status.toString),
      List("AccessExactly" -> "proven", "TokenNamesHolder" -> "proven", "AccessNeedsGrant" -> "proven", "GrantLetsIn" -> "proven", "DecisionContract" -> "proven"))
    assertEquals(r.head._2.obligations.find(_.name == "root_impl").map(_.status.toString), Some("proven"))
    assertEquals(checked.after.generate.trusted, Nil)
    assert(w.flatMap(_.context(decisionContract)).unsafeRunSync().text.contains("No user may ever"))
  }
