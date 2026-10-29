package frflow.testing.ported

import auth.*
import frflow.*
import frflow.core.expr.Value
import frflow.eval.run.Broken
import frflow.testing.report.{Against, Failure}
import frflow.core.name.NodeId

/** Auth's generated tests (today's `AuthSuite`, its testing cases' names kept): `admit`'s plain code against every
  * claim on it, on generated grant and session tables, tokens and paths; and the seeded `careless` decision.
  */
class AuthSuite extends munit.FunSuite:
  // A thousand generated cases a claim, the suites beside it running at once: on CI's two cores, minutes, not 30 s.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(5, "minutes")
  test("the decision is tested against its contract: every generated case meets it, every part of it is reached") {
    assertEquals(Tested.nodes(knowledge).sorted,
      List("accessNeedsGrant", "decisionContract", "grantLetsIn", "tokenNamesHolder"))
    Tested.nodes(knowledge).foreach { n =>
      assertEquals(Tested.passes(knowledge, n, List(DecisionExamples())).against, Against.Claim(NodeId(n)), n)
    }
  }

  test("an implementation that ignores the grant table fails a generated case, shrunk to its smallest") {
    val careless = FrModel("Auth")(knowledge.nodes*).implementProvided(grants, sessions)
      .implementTested(admit)(env => (t, _) => env(sessions).open.find(_.token == t).map(_.user))
    // A token issued to a user, no grant at all: the user is let in.
    Tested.failure(careless, "decisionContract") match
      case Failure.Call(List(Value.Str(token), _), givens, Broken.Post, _) =>
        val byName = givens.map(g => g.symbol.value -> g.value).toMap
        assertEquals(byName.get("grants"), Some(Value.Many(Nil)))
        val held = byName.get("sessions").collect { case Value.Data(_, List(Value.Many(open))) => open }
        assertEquals(held.map(_.size), Some(1))
        assert(held.exists(_.exists { case Value.Data(_, List(Value.Str(`token`), _)) => true; case _ => false }), held)
      case other => fail(s"not shrunk: $other")
  }

  test("the examples pass against the implementation") {
    assertEquals(Tested.onCode(DecisionExamples()).distinct, List(frflow.eval.run.OnCode.Holds))
  }
