package frflow.decision

import frflow.decision.content.Sha
import frflow.decision.ledger.{Decider, Deciders, LedgerBase, Seal, Seals}

/** The ledger's base is signed like the deciders' list: a version counts only when a listed key signed it and it
  * names the one before; the history a ledger is counted against starts at the last committed text it accepts.
  */
class LedgerBaseSuite extends munit.FunSuite:
  private def sign(key: String)(bytes: Array[Byte]): Seal = Seal(key, s"$key:${Sha(String(bytes, "UTF-16"))}")
  private val verify: Seals.Verifier = (s, bytes) => s.signature == sign(s.key)(bytes).signature
  private val deciders = Some(Deciders(List(Decider("ann", "k1", "public-1")), None, None))

  private def base(text: String, before: Option[LedgerBase], key: String): LedgerBase =
    val b = LedgerBase.of(text, before)
    b.copy(seal = Some(sign(key)(b.payload)))

  test("a base counts only when signed by a listed key, after the base before it, and with a deciders' list") {
    val first = base("v2", None, "k1")
    assertEquals(LedgerBase.committed(List(first), deciders, verify), Some(first))
    assertEquals(LedgerBase.committed(List(base("v2", None, "k2")), deciders, verify), None)
    assertEquals(LedgerBase.committed(List(first), None, verify), None)
    val second = base("v3", Some(first), "k1")
    assertEquals(LedgerBase.committed(List(first, second), deciders, verify), Some(second))
    assertEquals(LedgerBase.committed(List(first, base("v3", None, "k1")), deciders, verify), None)
  }

  test("the history starts at the last committed text the base accepts; all of it without one, or when none is") {
    val texts = List("v1", "v2", "v3", "v2", "v4")
    assertEquals(LedgerBase.from(texts, Some(base("v2", None, "k1"))), List("v2", "v4"))
    assertEquals(LedgerBase.from(texts, None), texts)
    assertEquals(LedgerBase.from(texts, Some(base("v9", None, "k1"))), texts)
  }
