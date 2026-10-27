package frflow.decision

import frflow.decision.ledger.*
import frflow.decision.review.{Reading, ReviewState}
import Shelf.*

/** Only the decisions that count are folded into the review states: signed by a key listed under the decider's name,
  * verifying, on a node whose committed history is where its history now starts; the others are said, with why.
  */
class CountedSuite extends munit.FunSuite:
  private val (dev, other) = (TestKey(), TestKey())
  private val verify = TestKey.verifier(dev, other)
  private val deciders = Deciders(List(Decider("dev", dev.id, "")), None, None)

  private def accepted(l: Ledger, node: String, i: Int, key: TestKey): Ledger =
    val d = Decision.taken(Action.Accept, by(i), Reason("it says what is meant", Nil), Reading(shelf, l).bound(
      shelf.get(id(node)).getOrElse(fail(node))))
    Seals.signAdded(l, l.add(id(node), d), key.sign)

  private val signed = accepted(Ledger.empty, "R", 1, dev)

  test("a decision signed by a listed decider counts; the root is accepted") {
    val c = Counted.of(signed, Some(deciders), verify, None)
    assertEquals((c.counting, c.others), (signed, Nil))
    assertEquals(Reading(shelf, c.counting).state(id("R")), ReviewState.Accepted)
  }

  test("signed by a key not listed under the decider's name, it does not count, and is said so") {
    val c = Counted.of(accepted(Ledger.empty, "R", 1, other), Some(deciders), verify, None)
    assertEquals((c.counting, c.others.map(x => (x._1, x._3))), (Ledger.empty, List(id("R") -> Uncounted.NotListed)))
    assertEquals(Reading(shelf, c.counting).state(id("R")), ReviewState.Proposed)
  }

  test("changed after it was signed, it does not verify; with no deciders' list, nothing counts") {
    val changed = Ledger(signed.decisions.view.mapValues(_.map(d => d.copy(reason = Reason("another", Nil)))).toMap)
    assertEquals(Counted.of(changed, Some(deciders), verify, None).others.map(_._3), List(Uncounted.NotVerified))
    assertEquals(Counted.of(signed, None, verify, None).others.map(_._3), List(Uncounted.NoDeciders))
  }

  test("a node whose last decisions were taken out since the commit counts none of its decisions") {
    val committed = accepted(signed, "R", 2, dev)
    val c = Counted.of(signed, Some(deciders), verify, Some(committed))
    assertEquals(c.others.map(x => (x._1, x._3)), List(id("R") -> Uncounted.Rewritten))
    assertEquals(Counted.of(committed, Some(deciders), verify, Some(signed)).others, Nil)
  }

  test("what a decision on the ledger as it counts adds is stored after every decision kept, those not counting too") {
    val working = accepted(Ledger.empty, "R", 1, other)
    val counted = Counted.of(working, Some(deciders), verify, None).counting
    val after = accepted(counted, "R", 2, dev)
    val stored = Counted.stored(working, counted, after)
    assertEquals(stored.history(id("R")).size, 2)
    assertEquals(Counted.of(stored, Some(deciders), verify, None).counting.history(id("R")),
      after.history(id("R")))
  }
