package frflow.decision

import frflow.decision.ledger.{Action, Decision, Ledger, Payload, Reason, Seals}
import frflow.decision.review.Reading
import Shelf.*

/** Decisions signed with a key made in memory for the test: the developer's own key is never read. */
class SealsSuite extends munit.FunSuite:
  private val key = TestKey()
  private val verify = TestKey.verifier(key)
  private def decision(reason: String) =
    Decision.taken(Action.Accept, by(1), Reason(reason, Nil), Reading(shelf, Ledger.empty).bound(r))
  private def signed(reason: String) =
    Seals.signAdded(Ledger.empty, Ledger.empty.add(id("R"), decision(reason)), key.sign)
  private def verifies(l: Ledger, node: String) =
    l.current(id(node)).exists(d => d.seal.exists(verify(_, Payload.of(id(node), d))))

  test("a signed decision verifies; changed, or signed by another key, it does not") {
    val l = signed("it is the purpose, stated")
    assert(verifies(l, "R"))
    val d = l.current(id("R")).get
    assert(!d.seal.exists(verify(_, Payload.of(id("A"), d))))
    assert(!d.seal.exists(verify(_, Payload.of(id("R"), d.copy(reason = Reason("another reason", Nil))))))
    assert(!d.seal.exists(TestKey.verifier(TestKey())(_, Payload.of(id("R"), d))))
    assert(!verifies(Ledger.empty.add(id("R"), decision("it is the purpose, stated")), "R"))
  }

  test("the developer's new decisions are signed; those before are kept as they were") {
    val before = Ledger.empty.add(id("R"), decision("it is the purpose, stated"))
    val after = before.add(id("R"), decision("it still is the purpose")).add(id("A"), decision("it makes the root"))
    val l = Seals.signAdded(before, after, key.sign)
    assertEquals(l.history(id("R")).map(_.seal.isDefined), List(false, true))
    assert(verifies(l, "R") && verifies(l, "A"))
    // A later decision names the one it follows, so its seal covers the order.
    assertEquals(l.current(id("R")).flatMap(_.after), Some(Ledger.entry(before.history(id("R")).head)))
  }
