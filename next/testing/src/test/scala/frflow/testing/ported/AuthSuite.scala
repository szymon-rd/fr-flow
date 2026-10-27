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
  test("the decision is tested against its contract: every generated case meets it, every part of it is reached") {
    assertEquals(Tested.nodes(knowledge).sorted,
      List("accessNeedsGrant", "decisionContract", "grantLetsIn", "tokenNamesHolder"))
    Tested.nodes(knowledge).foreach { n =>
      val r = Tested.report(knowledge, n, List(DecisionExamples())).getOrElse(fail(s"$n is not tested"))
      assertEquals((r.failure, r.unreached, r.cases, r.against), (None, Nil, 1000, Against.Claim(NodeId(n))), n)
    }
  }

  test("an implementation that ignores the grant table fails a generated case, shrunk to its smallest") {
    val careless = KnowledgeBase("Auth")(knowledge.nodes*).implementProvided(grants, sessions)
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
