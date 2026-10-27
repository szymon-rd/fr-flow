package frflow.decision

import frflow.core.name.NodeId
import frflow.decision.content.{Chain, Content, Sha}
import frflow.decision.ledger.{Action, Authorship, Bound, Decider, Deciders, Decision, Payload, Reason, Seal, Seals}
import java.time.Instant

/** Who may decide is a committed list the developer signs: a key filed under a new name decides nothing, and an old
  * version committed again restores no one.
  */
class DecidersSuite extends munit.FunSuite:
  /** A stand-in for signatures: the key's id and the payload's hash. */
  private def sign(key: String)(bytes: Array[Byte]): Seal = Seal(key, s"$key:${Sha(String(bytes, "UTF-8"))}")
  private val verify: Seals.Verifier = (s, bytes) => s.signature == sign(s.key)(bytes).signature

  private def version(after: Option[Deciders], signer: String, entries: Decider*): Deciders =
    val unsigned = Deciders(entries.toList, after.map(_.ref), None)
    unsigned.copy(seal = Some(sign(signer)(unsigned.payload)))
  private val (ann, agent) = (Decider("ann", "k1", "public-1"), Decider("agent", "k2", "public-2"))
  private val first = version(None, "k1", ann)
  private val node = NodeId("Root")

  private def decided(by: String, key: String): Decision =
    val d = Decision.taken(Action.Accept, Authorship(by, Instant.EPOCH, None), Reason("it states the purpose", Nil),
      Bound(Content.empty, Chain.empty, None))
    d.copy(seal = Some(sign(key)(Payload.of(node, d))))

  test("a decision counts only when signed by the key listed under its decider's name") {
    assert(first.counts(verify)(node, decided("ann", "k1")))
    assert(!first.counts(verify)(node, decided("ann", "k2")))
    assert(!first.counts(verify)(node, decided("agent", "k2")))
  }

  test("a new list counts only when signed by a key the list before it held") {
    assertEquals(Deciders.committed(List(first, version(Some(first), "k1", ann, agent)), verify).map(_.entries.size),
      Some(2))
    assertEquals(Deciders.committed(List(first, version(Some(first), "k2", ann, agent)), verify), None)
  }

  test("a first list counts only when signed by its own first entry") {
    assert(Deciders.committed(List(version(None, "k1", ann, agent)), verify).isDefined)
    assertEquals(Deciders.committed(List(version(None, "k2", ann, agent)), verify), None)
  }

  test("a list with no seal follows none, even after a list it names") {
    assertEquals(Deciders.committed(List(first.copy(seal = None)), verify), None)
    val unsealed = version(Some(first), "k1", ann, agent).copy(seal = None)
    assertEquals(Deciders.committed(List(first, unsealed), verify), None)
  }

  test("an earlier list committed again does not restore a decider the list removed") {
    val withAgent = version(Some(first), "k1", ann, agent)
    val revoked = version(Some(withAgent), "k1", ann)
    assertEquals(Deciders.committed(List(first, withAgent, revoked), verify).map(_.entries), Some(List(ann)))
    assertEquals(Deciders.committed(List(first, withAgent, revoked, withAgent), verify), None)
  }
