package frflow.project.services

import auth.*
import frflow.*
import frflow.core.expr.Value
import frflow.eval.run.{Broken, OnCode}
import frflow.proof.audit.Completeness
import frflow.project.{Live, Ported, Projects}
import frflow.project.Ported.Lean
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.{ObligationStatus, Result}
import frflow.testing.Tested
import frflow.testing.report.Failure
import scala.concurrent.duration.*

/** Auth checked whole: by Lean and by tests (1,000 cases from seed 1), every node proven and every consistency
  * group proven (owner §28); the seeded bug is caught; and the examples hold on the code.
  */
class AuthPortSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 40.minutes
  private val elaborated = Projects.elaborated(knowledge)

  private val proofs = List("Lemmas", "accessExactly", "tokenNamesHolder", "accessNeedsGrant", "grantLetsIn")
  private val lean = Lean(proofs.map(n => n -> Ported.proof("auth", "Auth", n)), Nil, None)

  test("checked by Lean and tested: every node is proven, and the theory is consistent".tag(Live)) {
    Ported.run(elaborated, DecisionExamples().elaborated.fold(e => fail(e.toString), identity), lean, Nil).map { r =>
      val a = r.analysis
      assertEquals(Completeness.of(a.decided, a.modules), Nil)
      assertEquals(Ported.unproven(a), Map.empty[String, List[String]])
      val whole = a.wholeCheck.map(_.results).getOrElse(fail("the theory's own check is not recorded"))
      assertEquals(whole.collect { case Result(n @ ObligationName.Consistent(_), s, _) => n -> s }.toMap,
        a.groups.map((i, _) => ObligationName.Consistent(i) -> ObligationStatus.Proven).toMap)
    }
  }

  test("the seeded bug: a decision that ignores the grant table fails a generated case of decisionContract") {
    val careless = FrModel("Auth")(knowledge.nodes*).defining(grants.provided, sessions.provided)
      .defining(admit.defineTested(env => (t, _) => env(sessions).open.find(_.token == t).map(_.user)))
    Tested.failure(careless, "decisionContract") match
      case Failure.Call(List(Value.Str(_), _), _, Broken.Post, _) => ()
      case other                                                 => fail(s"not caught: $other")
  }

  test("today's examples hold on the code, each checked in Scala only (it sets the tables)") {
    assertEquals(Tested.onCode(DecisionExamples()), List.fill(5)(OnCode.Holds))
  }

  test("the code is tested with today's seed and cases: every claim on admit, 1,000 cases from seed 1") {
    assertEquals(Tested.nodes(knowledge).map(n => n -> Tested.passes(knowledge, n, List(DecisionExamples())).seed
      .value).toMap, Map("tokenNamesHolder" -> 1L, "accessNeedsGrant" -> 1L, "grantLetsIn" -> 1L,
      "decisionContract" -> 1L))
  }

  test("the server decides a request by admit's code, given the tables: Alice's token and grant let her in") {
    val decide = service(List(Grant(UserId("alice"), Path("/a"))), Sessions(List(Session("t1", UserId("alice")))))
    assertEquals((decide("t1", Path("/a")), decide("t1", Path("/b"))), (Some(UserId("alice")), None))
  }
